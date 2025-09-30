/*
 * minibash - an open-ended subset of bash
 *
 * Developed by Godmar Back for CS 3214 Fall 2025
 * Virginia Tech.
 */
#define _GNU_SOURCE 1

#ifndef MB_DEBUG
# define DBG(...) ((void)0)
#else
# define DBG(...) fprintf(stderr, __VA_ARGS__)

#endif

#include "tree_sitter/tree-sitter-bash.h"
#include "ts_symbols.h"
#include <assert.h>
#include <errno.h>

#include <fcntl.h>

#include <stdio.h>
#include <readline/readline.h>
#include <stdbool.h>


#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <termios.h>
#include <tree_sitter/api.h>
#include <unistd.h>
/* Since the handed out code contains a number of unused functions. */
#pragma GCC diagnostic ignored "-Wunused-function"

#include "hashtable.h"
#include "list.h"
#include "signal_support.h"
#include "ts_helpers.h"
#include "utils.h"
#include <fcntl.h>
#include <spawn.h>
#include <sys/stat.h>



static inline void set_cloexec(int fd)
{
	int flags;

	if (fd >= 0)
	{
		flags = fcntl(fd, F_GETFD);
		if (flags != -1)
			(void)fcntl(fd, F_SETFD, flags | FD_CLOEXEC);
	}
}
static enum { LOOP_NONE, LOOP_BREAK, LOOP_CONTINUE } loop_ctl = LOOP_NONE;

/* These are field ids suitable for use in ts_node_child_by_field_id for certain rules.
   e.g., to obtain the body of a while loop, you can use:
	TSNode body = ts_node_child_by_field_id(child, bodyId);
*/
static TSFieldId bodyId, redirectId, destinationId, valueId, nameId, conditionId;
static TSFieldId variableId;
static TSFieldId leftId, operatorId, rightId;

static char *input;             // to avoid passing the current input around
static TSParser *parser;        // a singleton parser instance
static tommy_hashdyn shell_vars;
	// a hash table containing the internal shell variables

static void handle_child_status(pid_t pid, int status);
static char *read_script_from_fd(int readfd);
static void execute_script(char *script);
extern char **environ;

/* ---- forward decls used by condition evaluation ---- */
static void execute_command(TSNode command_node);
struct redir_spec; /* forward declare so prototype can use it */
static void execute_pipeline(TSNode pipeline, const struct redir_spec *opt_r);
static void run_program(TSNode program);

/* Single global used by condition eval (already used elsewhere) */
static int last_exit_status = 0; // Track exit status of last command

/* Evaluate a condition node (bash semantics: 0 == true) */
static int eval_condition_node(TSNode n) {
    if (ts_node_is_null(n)) { last_exit_status = 1; return last_exit_status; }
    const char *t = ts_node_type(n);
    if (t && strcmp(t, "command") == 0) {
        execute_command(n);
    } else if (t && strcmp(t, "pipeline") == 0) {
        execute_pipeline(n, NULL);
    } else if (t && strcmp(t, "list") == 0) {
        run_program(n);
    } else {
        last_exit_status = 1;
    }
    return last_exit_status;
}


static unsigned long khash(const void *key)
{
	return (tommy_hash_u32(0, key, strlen((const char *)key)));
}

static char *str_cat3(char *a, const char *b) {
    if (!a && !b) return strdup("");
    if (!a) return strdup(b ? b : "");
    if (!b) return a;
    size_t la = strlen(a), lb = strlen(b);
    a = realloc(a, la + lb + 1);
    memcpy(a + la, b, lb);
    a[la + lb] = 0;
    return a;
}
/* expansions & vars */
static char *command_subst_to_text(TSNode cs);
static const char *var_get(const char *k);
static void var_set(const char *k, const char *v);
static void execute_pipeline(TSNode pipeline, const struct redir_spec *opt_r);
static void run_program(TSNode program);




struct	kv
{
	tommy_node node;
	char *k;
	char *v;
};

static unsigned	kv_hash(const char *s)
{
	return (tommy_hash_u32(0, s, (unsigned)strlen(s)));
}

static int kv_cmp(const void *a, const void *b)
{
    const struct kv *p = (const struct kv *)a;  // node->data
    const char *key = (const char *)b;          // the lookup key
    if (!p || !p->k || !key) return -1;
    return strcmp(p->k, key);
}

static void var_set(const char *k, const char *v)
{
	tommy_node	*n;
	struct kv	*p;

	if (!k)
		return ;
	n = tommy_hashdyn_search(&shell_vars, kv_cmp, k, kv_hash(k));
	if (n)
	{
		p = n->data;
		free(p->v);
		p->v = strdup(v ? v : "");
		setenv(k, p->v, 1);
		return ;
	}
	p = calloc(1, sizeof *p);
	p->k = strdup(k); // Make sure k is not NULL before strdup
	p->v = strdup(v ? v : "");
	tommy_hashdyn_insert(&shell_vars, &p->node, p, kv_hash(p->k));
	setenv(p->k, p->v, 1);
}

static const char *var_get(const char *k)
{
	tommy_node	*n;
	const char	*e = getenv(k);

	if (!k)
		return ("");
	n = tommy_hashdyn_search(&shell_vars, kv_cmp, k, kv_hash(k));
	if (n)
		return (((struct kv *)n->data)->v);
	return (e ? e : "");
}

static void kv_free(void *vp)
{
	struct kv *p;

	p = vp;
	free(p->k);
	free(p->v);
	free(p);
}
static char *command_subst_to_text(TSNode cs)
{
	uint32_t					start;
	uint32_t					end;
	char						*raw;

	char *inner = NULL;


	size_t	L;
	int p[2];
	pid_t pid;
	posix_spawn_file_actions_t fa;
	posix_spawnattr_t attr;
//	char *argv[] = {"sh", "-c", inner, NULL};
	int	rc;
	char	*buf;
	size_t	cap = 0, len;
	char	tmp[4096];
	ssize_t	r;
	int status;

	// TODO(next): verify concatenation with surrounding word segments (040)
	// Consider collapsing multiple spaces/newlines if tests require it (keep exactly bash-like).
	/* Grab the full text of the node and strip $() or backticks by scanning children; simplest is:
		use start/end byte positions to slice from input,
			then heuristically strip "$(" .. ")" or '`' .. '`'.
		Safer: find the child that is the command body: often named 'command' or 'list'.
		let /bin/sh parse. */
	start = ts_node_start_byte(cs);
	end = ts_node_end_byte(cs);
	if (end <= start)
		return (strdup(""));
	/* Slice, then remove outer $() or backticks */
	raw = strndup(input + start, end - start);
	inner = raw;
	L = strlen(raw);
	if (L >= 3 && raw[0] == '$' && raw[1] == '(' && raw[L - 1] == ')')
	{
		inner = strndup(raw + 2, L - 3);
		free(raw);
	}
	else if (L >= 2 && raw[0] == '`' && raw[L - 1] == '`')
	{
		inner = strndup(raw + 1, L - 2);
		free(raw);
	}
	else
	{
		inner = raw; /* unknown wrapper; try as-is */
	}
	DBG("Running command substitution: %s\n", inner); // ADD HERE
	/* Run /bin/sh -c "<inner>" and capture stdout */
	if (pipe(p) != 0)
		return (strdup(""));


	
	posix_spawn_file_actions_init(&fa);
	posix_spawnattr_init(&attr);
	posix_spawn_file_actions_adddup2(&fa, p[1], STDOUT_FILENO);
	posix_spawn_file_actions_addclose(&fa, p[0]);
	posix_spawn_file_actions_addclose(&fa, p[1]);

        char *argv[] = { "sh", "-c", inner, NULL };
	rc = posix_spawnp(&pid, "sh", &fa, &attr, argv, environ);
	posix_spawn_file_actions_destroy(&fa);
	posix_spawnattr_destroy(&attr);
	close(p[1]);
	if (rc != 0)
	{
		close(p[0]);
		free(inner);
		return (strdup(""));
	}
	/* Read all stdout */
	buf = NULL;
	cap = 0, len = 0;
	while ((r = read(p[0], tmp, sizeof tmp)) > 0)
	{
		if (len + (size_t)r + 1 > cap)
		{
			cap = (cap ? cap * 2 : 8192);
			if (cap < len + r + 1)
				cap = len + r + 1;
			buf = realloc(buf, cap);
		}
		memcpy(buf + len, tmp, (size_t)r);
		len += (size_t)r;
	}
	close(p[0]);
	if (!buf)
	{
		buf = strdup("");
		len = 0;
	}
	else
		buf[len] = 0;
	waitpid(pid, &status, 0);
	DBG("Command substitution result: len=%zu, content='%s'\n", len, buf);
		// ADD HERE
	free(inner);
	/* Trim one trailing newline (bash behavior in command substitution) */
	if (len > 0 && buf[len - 1] == '\n')
		buf[--len] = 0;
	return (buf);
}

/* Expand a node to text, respecting quoting & expansions */
static char *expand_node_to_text(TSNode n)
{
    const char *t = ts_node_type(n);
    if (!t) return strdup("");

    /* single quotes: literal, strip quotes */
    if (strcmp(t, "raw_string") == 0) {
        char *withq = ts_extract_node_text(input, n);
        if (!withq) return strdup("");
        size_t len = strlen(withq);
        char *out = (len >= 2) ? strndup(withq + 1, len - 2) : strdup("");
        free(withq);
        return out;
    }

    /* double quotes: children may be string_content, expansions, cmd subs */
    if (strcmp(t, "string") == 0) {
        char *out = NULL;

        /* Use only *named* children; ignore the quote tokens */
        uint32_t named = ts_node_named_child_count(n);
        for (uint32_t i = 0; i < named; i++) {
            TSNode c = ts_node_named_child(n, i);
            const char *ct = ts_node_type(c);
            if (!ct) continue;

            if (strcmp(ct, "string_content") == 0) {
                char *s = ts_extract_node_text(input, c);
                out = str_cat3(out, s);
                free(s);
            } else if (strcmp(ct, "simple_expansion") == 0) {
                TSNode inner = ts_node_child(c, 1);
                char *val = NULL;
                if (!ts_node_is_null(inner)) {
                    const char *it = ts_node_type(inner);
                    if (it && strcmp(it, "special_variable_name") == 0) {
                        char *nm = ts_extract_node_text(input, inner);
                        if (nm) {
                            if (strcmp(nm, "?") == 0) {
                                char buf[16];
                                snprintf(buf, sizeof buf, "%d", last_exit_status);
                                val = strdup(buf);
                            } else if (strcmp(nm, "$") == 0) { // <-- FIX: Handle $$
                                char buf[16];
                                snprintf(buf, sizeof buf, "%d", getpid());
                                val = strdup(buf);
                            }
                            free(nm);
                        }
                    } else if (it && strcmp(it, "variable_name") == 0) {
                        char *nm = ts_extract_node_text(input, inner);
                        if (nm) { val = strdup(var_get(nm)); free(nm); }
                    }
                }
                if (!val) val = strdup("");
                out = str_cat3(out, val);
                free(val);
            } else if (strcmp(ct, "expansion") == 0) {
                TSNode var_node = ts_node_named_child(c, 0);
                char *val = NULL;
                if (!ts_node_is_null(var_node)) {
                    const char *vt = ts_node_type(var_node);
                    if (vt && strcmp(vt, "variable_name") == 0) {
                        char *nm = ts_extract_node_text(input, var_node);
                        if (nm) { val = strdup(var_get(nm)); free(nm); }
                    }
                }
                if (!val) val = strdup("");
                out = str_cat3(out, val);
                free(val);
            } else if (strcmp(ct, "command_substitution") == 0) {
                char *s = command_subst_to_text(c);
                out = str_cat3(out, s);
                free(s);
            }
        }

        /* Fallback: no named children (e.g., "abc" with no string_content) */
        if (!out) {
            char *withq = ts_extract_node_text(input, n);
            if (!withq) return strdup("");
            size_t len = strlen(withq);
            out = (len >= 2) ? strndup(withq + 1, len - 2) : strdup("");
            free(withq);
        }
        return out;
    }

    /* $VAR or $? in unquoted context */
    if (strcmp(t, "simple_expansion") == 0) {
        TSNode inner = ts_node_child(n, 1);
        if (!ts_node_is_null(inner)) {
            const char *it = ts_node_type(inner);
            if (it && strcmp(it, "special_variable_name") == 0) {
                char *nm = ts_extract_node_text(input, inner);
                if (nm) {
                    if (strcmp(nm, "?") == 0) {
                        char buf[16];
                        snprintf(buf, sizeof buf, "%d", last_exit_status);
                        free(nm);
                        return strdup(buf);
                    } else if (strcmp(nm, "$") == 0) { // <-- FIX: Handle $$
                        char buf[16];
                        snprintf(buf, sizeof buf, "%d", getpid());
                        free(nm);
                        return strdup(buf);
                    }
                    free(nm);
                }
                return strdup("");
            } else if (it && strcmp(it, "variable_name") == 0) {
                char *nm = ts_extract_node_text(input, inner);
                char *s = nm ? strdup(var_get(nm)) : strdup("");
                free(nm);
                return s;
            }
        }
        return strdup("");
    }

    /* ${VAR} */
    if (strcmp(t, "expansion") == 0) {
        TSNode var_node = ts_node_named_child(n, 0);
        if (!ts_node_is_null(var_node)) {
            const char *vt = ts_node_type(var_node);
            if (vt && strcmp(vt, "variable_name") == 0) {
                char *nm = ts_extract_node_text(input, var_node);
                char *val = nm ? strdup(var_get(nm)) : strdup("");
                free(nm);
                return val;
            }
        }
        return strdup("");
    }

    /* $(cmd) or `cmd` in unquoted context */
    if (strcmp(t, "command_substitution") == 0) {
        return command_subst_to_text(n);
    }

    /* word may be composite (children) or plain */
    if (strcmp(t, "word") == 0) {
        uint32_t sc = ts_node_child_count(n);
        if (sc == 0) {
            char *w = ts_extract_node_text(input, n);
            return w ? w : strdup("");
        }
        char *out = NULL;
        for (uint32_t i = 0; i < sc; i++) {
            TSNode c = ts_node_child(n, i);
            char *part = expand_node_to_text(c);
            out = str_cat3(out, part);
            free(part);
        }
        if (!out) out = strdup("");
        return out;
    }

    /* default: raw text */
    char *txt = ts_extract_node_text(input, n);
    return txt ? txt : strdup("");
}

/*static void hash_free(void *vp) {
	struct kv *p = vp;
	free(p->k); free(p->v); free(p);
}*/

static void	usage(char *progname)
{
	printf("Usage: %s -h\n"
			" -h            print this help\n",
			progname);
	exit(EXIT_SUCCESS);
}

/* Build a prompt */
static char	*build_prompt(void)
{
	return strdup("minibash> ");
}

/* Possible job status's to use.
 *
 * Some are specific to interactive job control which may not be needed
 * for this assignment.
 */
enum					job_status
{
	FOREGROUND,            /* job is running in foreground. Only one job can be
								in the foreground state. */
	BACKGROUND,            /* job is running in background */
	STOPPED,               /* job is stopped via SIGSTOP */
	NEEDSTERMINAL,         /* job is stopped because it was a background job
								and requires exclusive terminal access */
	TERMINATED_VIA_EXIT,   /* job terminated via normal exit. */
	TERMINATED_VIA_SIGNAL /* job terminated via signal. */
};

struct					job
{
	struct list_elem elem;  /* Link element for jobs list. */
	int jid;                /* Job id. */
	enum job_status status; /* Job status. */
	int num_processes_alive;
		/* The number of processes that we know to be alive */
	pid_t				pgid;
	int					nprocs;
	pid_t				pids[64];
	/* Add additional fields here as needed. */
};

/* Utility functions for job list management.
 * We use 2 data structures:
 * (a) an array jid2job to quickly find a job based on its id
 * (b) a linked list to support iteration
 */
#define MAXJOBS (1 << 16)
static struct list		job_list;

static struct job		*jid2job[MAXJOBS];

/* Return job corresponding to jid */
static struct job	*get_job_from_jid(int jid)
{
	if (jid > 0 && jid < MAXJOBS && jid2job[jid] != NULL)
		return jid2job[jid];
	return NULL;
}

/* Allocate a new job, optionally adding it to the job list. */
static struct job	*allocate_job(bool includeinjoblist)
{
	struct job	*job;

	job = malloc(sizeof *job);
	job->num_processes_alive = 0;
	job->jid = -1;
	if (!includeinjoblist)
		return job;
	list_push_back(&job_list, &job->elem);
	for (int i = 1; i < MAXJOBS; i++)
	{
		if (jid2job[i] == NULL)
		{
			jid2job[i] = job;
			job->jid = i;
			return job;
		}
	}
	fprintf(stderr, "Maximum number of jobs exceeded\n");
	abort();
	return NULL;
}

/* Delete a job.
 * This should be called only when all processes that were
 * forked for this job are known to have terminated.
 */
static void	delete_job(struct job *job, bool removeFromJobList)
{
	int	jid;

	if (removeFromJobList)
	{
		jid = job->jid;
		assert(jid != -1);
		assert(jid2job[jid] == job);
		jid2job[jid]->jid = -1;
		jid2job[jid] = NULL;
	}
	else
	{
		assert(job->jid == -1);
	}
	/* add any other job cleanup here. */
	free(job);
}
/* Redirection description for one process */
struct					redir_spec
{
	const char *in_path;    // < file
	const char *out_path;   // > or >> file
	bool append_out;        // >>
	const char *err_path;   // 2> or 2>> file
	bool append_err;        // 2>>
	// --- New fields for file descriptor duplication (e.g., 2>&1) ---
	int dup_fd_target;      // The file descriptor to be redirected (e.g., 2 in 2>&1)
	int dup_fd_source;      // The file descriptor to duplicate from (e.g., 1 in 2>&1)
};

/*
 * Suggested SIGCHLD handler.
 *
 * Call waitpid() to learn about any child processes that
 * have exited or changed status (been stopped, needed the
 * terminal, etc.)
 * Just record the information by updating the job list
 * data structures. Since the call may be spurious (e.g.
 * an already pending SIGCHLD is delivered even though
 * a foreground process was already reaped), ignore when
 * waitpid returns -1.
 * Use a loop with WNOHANG since only a single SIGCHLD
 * signal may be delivered for multiple children that have
 * exited. All of them need to be reaped.
 */
static void	sigchld_handler(int sig, siginfo_t *info, void *_ctxt)
{
	pid_t	child;
	int		status;

	assert(sig == SIGCHLD);
	while ((child = waitpid(-1, &status, WUNTRACED | WNOHANG)) > 0)
	{
		handle_child_status(child, status);
	}
}

/* Wait for all processes in this job to complete, or for
 * the job no longer to be in the foreground.
 *
 * You should call this function from where you wait for
 * jobs started without the &; you would only use this function
 * if you were to implement the 'fg' command (job control only).
 *
 * Implement handle_child_status such that it records the
 * information obtained from waitpid() for pid 'child.'
 *
 * If a process exited, it must find the job to which it
 * belongs and decrement num_processes_alive.
 *
 * However, note that it is not safe to call delete_job
 * in handle_child_status because wait_for_job assumes that
 * even jobs with no more num_processes_alive haven't been
 * deallocated. You should postpone deleting completed
 * jobs from the job list until when your code will no
 * longer touch them.
 *
 * The code below relies on `job->status` having been set to FOREGROUND
 * and `job->num_processes_alive` having been set to the number of
 * processes successfully forked for this job.
 */
static void	wait_for_job(struct job *job)
{
		int status;
	pid_t	child;

	assert(signal_is_blocked(SIGCHLD));
	while (job->status == FOREGROUND && job->num_processes_alive > 0)
	{
		child = waitpid(-1, &status, WUNTRACED);
		// When called here, any error returned by waitpid indicates a logic
		// bug in the shell.
		// In particular, ECHILD "No child process" means that there has
		// already been a successful waitpid() call that reaped the child, so
		// there's likely a bug in handle_child_status where it failed to update
		// the "job" status and/or num_processes_alive fields in the required
		// fashion.
		// Since SIGCHLD is blocked, there cannot be races where a child's exit
		// was handled via the SIGCHLD signal handler.
		if (child != -1)
			handle_child_status(child, status);
		else
			utils_fatal_error("waitpid failed, see code for explanation");
	}
}

static void	execute_command(TSNode command_node)
{
	TSNode				name_node;
	uint32_t			child_count;
	char				**argv;
	int					argv_index;
	TSNode				child;
	struct job			*job;
	pid_t				pid;
	posix_spawnattr_t	attr;
	int					spawn_result;

	name_node = ts_node_child_by_field_id(command_node, nameId);
	if (ts_node_is_null(name_node))
	{
		name_node = ts_node_named_child(command_node, 0);
	}
	if (ts_node_is_null(name_node))
	{
		fprintf(stderr, "Error: No command name found\n");
		return ;
	}
	char *cmd_name = expand_node_to_text(name_node);
		// Changed to expand_node_to_text
	child_count = ts_node_named_child_count(command_node);
	argv = calloc(child_count + 1, sizeof(char *));
	if (!argv)
	{
		fprintf(stderr, "Memory allocation failed\n");
		free(cmd_name);
		return ;
	}
	argv[0] = cmd_name;
	argv_index = 1;
	for (uint32_t i = 1; i < child_count; i++)
	{
		child = ts_node_named_child(command_node, i);
		char *arg_text = expand_node_to_text(child);
			// Use expand_node_to_text for ALL arguments
		if (arg_text != NULL)
		{
			argv[argv_index++] = arg_text;
		}
	}
	argv[argv_index] = NULL;
	if (strcmp(cmd_name, "true") == 0)
	{
		last_exit_status = 0;
		for (int i = 0; i < argv_index; i++)
		{
			free(argv[i]);
		}
		free(argv);
		return ;
	}
	if (strcmp(cmd_name, "false") == 0)
	{
		last_exit_status = 1;
		for (int i = 0; i < argv_index; i++)
		{
			free(argv[i]);
		}
		free(argv);
		return ;
	}
	if (strcmp(cmd_name, "break") == 0) {
    		loop_ctl = LOOP_BREAK;
    		last_exit_status = 0;
    		for (int i = 0; i < argv_index; i++) free(argv[i]);
    		free(argv);
    		return;
	}
	if (strcmp(cmd_name, "continue") == 0) {
    		loop_ctl = LOOP_CONTINUE;
    	 	last_exit_status = 0;
    		for (int i = 0; i < argv_index; i++) free(argv[i]);
    		free(argv);
    		return;
	}

	if (strcmp(cmd_name, ":") == 0)
	{
		last_exit_status = 0; // : always succeeds
		for (int i = 0; i < argv_index; i++)
		{
			free(argv[i]);
		}
		free(argv);
		return ;
	}
	job = allocate_job(true);
	job->status = FOREGROUND;
	job->num_processes_alive = 1;
	job->nprocs = 1;
	posix_spawnattr_init(&attr);
	posix_spawnattr_setflags(&attr, POSIX_SPAWN_SETPGROUP);
	posix_spawnattr_setpgroup(&attr, 0);
	if (cmd_name[0] == '/')
	{
		spawn_result = posix_spawn(&pid, cmd_name, NULL, &attr, argv, environ);
	}
	else
	{
		spawn_result = posix_spawnp(&pid, cmd_name, NULL, &attr, argv, environ);
	}
	posix_spawnattr_destroy(&attr);
	if (spawn_result != 0)
	{
		fprintf(stderr, "minibash: %s: command not found\n", cmd_name);
		last_exit_status = 127;
		job->status = TERMINATED_VIA_EXIT;
		job->num_processes_alive = 0;
		delete_job(job, true);
	}
	else
	{
		job->pgid = pid;
		job->pids[0] = pid;
		job->nprocs = 1;
		wait_for_job(job);
		delete_job(job, true);
	}
	for (int i = 0; i < argv_index; i++)
	{
		free(argv[i]);
	}
	free(argv);
}
static void execute_pipeline(TSNode pipeline,
							const struct redir_spec *opt_r);
static char **build_argv_from_command(TSNode command_node,
							int *argc_out);
static void collect_redirs(TSNode redirected_stmt,
							struct redir_spec *r);

static int spawn_stage(const char *cmd0, char *const argv[],
							int rd_fd, int wr_fd, bool pipe_ampersand,
							const struct redir_spec *r, pid_t pgid_in,
							pid_t *out_pid, int pipes[][2], int npipes);

static char **build_argv_from_command(TSNode command_node, int *argc_out)
{
    int cap = 8, idx = 0;
    char **argv = calloc(cap, sizeof *argv);
    if (!argv) return NULL;

    /* Find the command name */
    TSNode name_node = ts_node_child_by_field_id(command_node, nameId);
    if (ts_node_is_null(name_node)) {
        name_node = ts_node_named_child(command_node, 0);
        if (ts_node_is_null(name_node)) {
            /* No name -> empty argv */
            if (argc_out) *argc_out = 0;
            free(argv);
            return NULL;
        }
    }

    /* argv[0] = expanded command name */
    if (idx + 2 > cap) { cap *= 2; argv = realloc(argv, cap * sizeof *argv); }
    argv[idx++] = expand_node_to_text(name_node);

    /* Append arguments: scan all named children; skip the name and redirections */
    uint32_t n = ts_node_named_child_count(command_node);
    for (uint32_t i = 0; i < n; i++) {
        TSNode child = ts_node_named_child(command_node, i);
        if (ts_node_eq(child, name_node)) continue;

        const char *t = ts_node_type(child);
        if (!t) continue;
        if (strcmp(t, "file_redirect") == 0) continue;
        if (strcmp(t, "command_name") == 0) continue;

        if (idx + 2 > cap) { cap *= 2; argv = realloc(argv, cap * sizeof *argv); }
        argv[idx++] = expand_node_to_text(child);
    }

    argv[idx] = NULL;
    if (argc_out) *argc_out = idx;
    return argv;
}

static void collect_redirs(TSNode redirected_stmt, struct redir_spec *r)
{
    // Initialize new fields (use -1 as sentinel for FDs)
    memset(r, 0, sizeof(*r));
    r->dup_fd_target = -1;
    r->dup_fd_source = -1;

    uint32_t n = ts_node_child_count(redirected_stmt);
    for (uint32_t i = 0; i < n; i++) {
        TSNode child = ts_node_child(redirected_stmt, i);
        const char *t = ts_node_type(child);
        if (!t || strcmp(t, "file_redirect") != 0) continue;

        /* -------- destination path (supporting expansions) -------- */
        char *path = NULL;
        TSNode dest = ts_node_child_by_field_id(child, destinationId);
        if (!ts_node_is_null(dest)) {
            path = expand_node_to_text(dest);
        }
        if (!path) path = strdup("");


        /* -------- operator token (supports numeric fds) -------- */
        char *op = NULL;
        TSNode opn = ts_node_child_by_field_id(child, redirectId);
        if (!ts_node_is_null(opn)) {
            op = ts_extract_node_text(input, opn);
        }
        if (!op) { free(path); continue; }

        /* forms: "<", ">", ">>", "1>", "1>>", "2>", "2>>", "0<", ">&" */
        int  target_fd = -1;    // -1 => default (stdout for '>', stdin for '<')
        bool is_append = false;
        bool is_input  = false;

        const char *p = op;
        if (p[0] >= '0' && p[0] <= '9' && (p[1] == '>' || p[1] == '<')) {
            target_fd = p[0] - '0';
            p += 1;
        }

        if (p[0] == '<') {
            is_input = true;
        } else if (p[0] == '>') {
            if (p[1] == '>') is_append = true;
        } else if (strcmp(op, ">&") == 0) {
            // The operator is just `>&` and the target FD is 1 (default)
            target_fd = (target_fd == -1) ? 1 : target_fd;
        } else if (strcmp(op, "<&") == 0) {
            // The operator is just `<&` and the target FD is 0 (default)
            is_input = true;
            target_fd = (target_fd == -1) ? 0 : target_fd;
        }


        // --- HANDLE DUPLICATION (e.g., 2>&1) ---
        if (path[0] == '&') {
            // It's a duplication: [FD]>&[FD]
            if (target_fd == -1) target_fd = is_input ? 0 : 1; // Default target
            
            // atoi reads the number after '&', e.g., for "&1", it reads 1.
            int source_fd = atoi(path + 1);

            // Store duplication details
            r->dup_fd_target = target_fd;
            r->dup_fd_source = source_fd;
            
            // Free the path string (which was actually &N) and the operator
            free(path);
            free(op);
            continue;
        }


        // --- HANDLE FILE REDIRECTION ---
        if (is_input || (target_fd == 0 && strchr(op, '<'))) {
            // Input redirection
            if (r->in_path) free((char *)r->in_path);
            r->in_path = path;
        } else {
            // Output redirection (default target is 1)
            if (target_fd == -1) target_fd = 1;

            if (target_fd == 2) { // Target FD is 2 (stderr)
                if (r->err_path) free((char *)r->err_path);
                r->err_path = path;
                r->append_err = is_append;
            } else { // Target FD is 1 (stdout) or other
                if (r->out_path) free((char *)r->out_path);
                r->out_path = path;
                r->append_out = is_append;
            }
        }

        free(op);
    }
}

static int	spawn_stage(const char *cmd0, char *const argv[], int rd_fd,
		int wr_fd, bool pipe_ampersand, const struct redir_spec *r,
		pid_t pgid_in, pid_t *out_pid, int pipes[][2], int npipes)

{
	posix_spawn_file_actions_t fa;
	posix_spawnattr_t attr;
	posix_spawn_file_actions_init(&fa);
	posix_spawnattr_init(&attr);

	/* 1) Wire pipeline dup2 first (stdin/stdout[/stderr]) */
	if (rd_fd >= 0)
		posix_spawn_file_actions_adddup2(&fa, rd_fd, STDIN_FILENO);
	if (wr_fd >= 0)
	{
		posix_spawn_file_actions_adddup2(&fa, wr_fd, STDOUT_FILENO);
		if (pipe_ampersand)
			posix_spawn_file_actions_adddup2(&fa, wr_fd, STDERR_FILENO);
	}

	/* 1.5) Apply FD duplication (e.g., 2>&1) */
	// Duplication must happen *before* file redirection if they target the same FD.
	// For instance, `cmd >file 2>&1` needs 2>&1 to happen after >file, but
	// `cmd 2>&1 >file` needs 2>&1 to happen first. bash prioritizes left-to-right.
	// Since we are applying all redirections simultaneously in the child,
	// the order in posix_spawn_file_actions is critical.
	// The problem is that the `file_redirect` nodes from Tree-sitter are unordered.
	// We assume, based on typical implementation, that duplication should happen first
	// to ensure it uses the established FD (like STDOUT_FILENO).
	if (r && r->dup_fd_target >= 0 && r->dup_fd_source >= 0) {
		posix_spawn_file_actions_adddup2(&fa, r->dup_fd_source, r->dup_fd_target);
	}

	/* 2) Apply file redirections (dup2 onto 0/1/2 as needed) */
	if (r)
	{
		if (r->in_path)
		{
			posix_spawn_file_actions_addopen(&fa, 100, r->in_path, O_RDONLY, 0);
			posix_spawn_file_actions_adddup2(&fa, 100, STDIN_FILENO);
			posix_spawn_file_actions_addclose(&fa, 100);
		}
		if (r->out_path)
		{
			int flags = O_WRONLY | O_CREAT | (r->append_out ? O_APPEND : O_TRUNC);
			posix_spawn_file_actions_addopen(&fa, 101, r->out_path, flags,
				0666);
			posix_spawn_file_actions_adddup2(&fa, 101, STDOUT_FILENO);
			posix_spawn_file_actions_addclose(&fa, 101);
		}
		if (r->err_path)
		{
			int flags = O_WRONLY | O_CREAT | (r->append_err ? O_APPEND : O_TRUNC);
			posix_spawn_file_actions_addopen(&fa, 102, r->err_path, flags,
				0666);
			posix_spawn_file_actions_adddup2(&fa, 102, STDERR_FILENO);
			posix_spawn_file_actions_addclose(&fa, 102);
		}
	}

	/* 3) Now that dup2 is set, close ALL pipe fds in the child,
		including rd_fd/wr_fd originals. This is handled by FD_CLOEXEC
		and explicit closing below. */

	if (pipes && npipes > 0)
	{
		for (int i = 0; i < npipes; i++)
		{
			int rfd = pipes[i][0], wfd = pipes[i][1];
			// Close pipe FDs the child *isn't* using, only if they are not the ones duped onto 0/1/2
			if (rfd >= 3 && rfd != rd_fd && rfd != wr_fd)
				posix_spawn_file_actions_addclose(&fa, rfd);
			if (wfd >= 3 && wfd != rd_fd && wfd != wr_fd)
				posix_spawn_file_actions_addclose(&fa, wfd);
		}
	}
	/* Always close the original pipe ends used by this stage (they were dup2’d already). */
	if (rd_fd >= 3)
		posix_spawn_file_actions_addclose(&fa, rd_fd);
	if (wr_fd >= 3)
		posix_spawn_file_actions_addclose(&fa, wr_fd);

	short flags = POSIX_SPAWN_SETPGROUP;
#ifdef POSIX_SPAWN_USEVFORK
	flags |= POSIX_SPAWN_USEVFORK;
#endif
	posix_spawnattr_setflags(&attr, flags);
	posix_spawnattr_setpgroup(&attr, pgid_in); // 0 => new pg leader

	pid_t cpid = -1;
	int s = (cmd0[0] == '/') ? posix_spawn(&cpid, cmd0, &fa, &attr,
			(char *const *)argv, environ) : posix_spawnp(&cpid, cmd0, &fa,
			&attr, (char *const *)argv, environ);

	posix_spawn_file_actions_destroy(&fa);
	posix_spawnattr_destroy(&attr);

	if (s != 0)
	{
		if (s == ENOENT)
			last_exit_status = 127;
		else if (s == EACCES)
			last_exit_status = 126;
		else
			last_exit_status = 127;
		fprintf(stderr, "minibash: %s: %s\n", cmd0, strerror(s));
		return -1;
	}
	*out_pid = cpid;
	return 0;
}

static void	execute_pipeline(TSNode pipeline, const struct redir_spec *opt_r)
{
	uint32_t			m;
	struct redir_spec	first_cmd_redir;
	TSNode				first_cmd;
	uint32_t			fc_count;
	TSNode				child;
	uint32_t			rc;
	TSNode				c;
	char				*tok;
	int					npipes;
	int					pipes[64][2];
	struct job			*job;
	TSNode				cmd_node;
	int					argc;
	char				**argv;
	int					rd_fd;
	int					wr_fd;
	struct redir_spec	rtmp;
	
	const struct redir_spec *r = NULL;
	pid_t pid;

	m = ts_node_named_child_count(pipeline);
	if (m == 0)
		return ;
	
	// --- 1. Setup Redirection Specs ---
	memset(&first_cmd_redir, 0, sizeof first_cmd_redir);
	first_cmd_redir.dup_fd_target = -1;
	first_cmd_redir.dup_fd_source = -1;

	first_cmd = ts_node_named_child(pipeline, 0);
	fc_count = ts_node_child_count(first_cmd);
	for (uint32_t k = 0; k < fc_count; k++)
	{
		child = ts_node_child(first_cmd, k);
		if (strcmp(ts_node_type(child), "file_redirect") == 0)
		{
			// Collect redirects applied directly to the first command.
			collect_redirs(first_cmd, &first_cmd_redir);
			break ; // Assume only one set of redirects per command node structure
		}
	}
	
	// --- 2. Setup Pipes and Job ---
	bool pipe_ampersand = false;
	rc = ts_node_child_count(pipeline);
	for (uint32_t i = 0; i < rc; i++)
	{
		c = ts_node_child(pipeline, i);
		if (ts_node_is_named(c))
			continue ;
		tok = ts_extract_node_text(input, c);
		if (tok && strcmp(tok, "|&") == 0)
			pipe_ampersand = true;
		free(tok);
	}
	npipes = (m > 1) ? (int)(m - 1) : 0;
	for (int i = 0; i < npipes; i++)
	{
		if (pipe(pipes[i]) < 0)
		{
			perror("pipe");
			return ;
		}
		set_cloexec(pipes[i][0]);
		set_cloexec(pipes[i][1]);
	}
	
	job = allocate_job(true);
	job->status = FOREGROUND;
	job->nprocs = (int)m;
	job->num_processes_alive = (int)m;
	job->pgid = 0;
	
	// --- 3. Spawn Stages ---
	for (uint32_t i = 0; i < m; i++)
	{
		cmd_node = ts_node_named_child(pipeline, i);
		argc = 0;
		argv = build_argv_from_command(cmd_node, &argc);
		
		if (!argv || !argv[0])
		{
			if (argv) { for (int k = 0; k < argc; k++) free(argv[k]); free(argv); }
			// If a command is missing, the whole pipeline fails.
			job->num_processes_alive = 0;
			delete_job(job, true);
			
			// Close all pipes on failure
			for (int p = 0; p < npipes; p++) { close(pipes[p][0]); close(pipes[p][1]); }
			return; 
		}
		
		rd_fd = (i == 0) ? -1 : pipes[i - 1][0];
		wr_fd = (i == m - 1) ? -1 : pipes[i][1];
		
		// Determine which redirection spec (r) to use for this stage
		r = NULL;
		memset(&rtmp, 0, sizeof rtmp);
		rtmp.dup_fd_target = -1;
		rtmp.dup_fd_source = -1;

		if (i == 0 && (first_cmd_redir.in_path || first_cmd_redir.dup_fd_target >= 0))
		{
			// Redirs explicitly on the *first* command (like `< file cmd1 | ...`)
			// Since collect_redirs runs on the whole command node, 
			// it should find input/output redirects on cmd1 itself.
			r = &first_cmd_redir;
		}
		else if (i == m - 1 && opt_r)
		{
			// Outer redirs (if present) apply ONLY to the *last* stage.
			rtmp.out_path = opt_r->out_path;
			rtmp.append_out = opt_r->append_out;
			rtmp.err_path = opt_r->err_path;
			rtmp.append_err = opt_r->append_err;
			rtmp.dup_fd_target = opt_r->dup_fd_target;
			rtmp.dup_fd_source = opt_r->dup_fd_source;
			r = &rtmp;
		}
		
		// Spawn the process
		if (spawn_stage(argv[0], argv, rd_fd, wr_fd, pipe_ampersand, r,
				job->pgid ? job->pgid : 0, &pid, pipes, npipes) < 0)
		{
			// Spawn failed, cleanup
			job->num_processes_alive = 0;
			delete_job(job, true);
			
			for (int p = 0; p < npipes; p++) { close(pipes[p][0]); close(pipes[p][1]); }
			for (int k = 0; k < argc; k++) free(argv[k]); free(argv);
			return ;
		}
		
		if (!job->pgid)
			job->pgid = pid;
		job->pids[i] = pid;
		
		// --- Parent closes FDs ---
		// The parent must close the pipe ends used for communication with this child.
		if (rd_fd >= 0)
			close(rd_fd);
		if (wr_fd >= 0)
			close(wr_fd);
		
		for (int k = 0; k < argc; k++) free(argv[k]);
		free(argv);
	}
	
	// FIX: The original, known-working solution for pipelines often involves 
	// closing all pipe FDs *after* the loop, assuming the per-stage closes 
	// might fail or be incomplete. Let's stick with the per-stage close in 
	// the loop above and rely on it working, as it's cleaner.
	
	// --- 4. Wait for Job ---
	wait_for_job(job);
	delete_job(job, true);
}

static struct job	*find_job_by_pid(pid_t pid, int *idx_out)
{
	struct job	*job;

	for (struct list_elem *e = list_begin(&job_list); e != list_end(&job_list); e = list_next(e))
	{
		job = list_entry(e, struct job, elem);
		for (int i = 0; i < job->nprocs; i++)
		{
			if (job->pids[i] == pid)
			{
				if (idx_out)
					*idx_out = i;
				return job;
			}
		}
	}
	return NULL;
}

static void	handle_child_status(pid_t pid, int status)
{
	int			idx;
	struct job	*job;
	bool		is_last_stage;

	assert(signal_is_blocked(SIGCHLD));
	idx = -1;
	job = find_job_by_pid(pid, &idx);
	if (!job)
	{
		// Could be a race or a child from a previous job already cleaned up.
		return ;
	}
	// Track exit for the *last* stage’s status like bash does
	is_last_stage = (idx == job->nprocs - 1);
	if (WIFEXITED(status))
	{
		if (is_last_stage)
			last_exit_status = WEXITSTATUS(status);
		job->num_processes_alive--;
	}
	else if (WIFSIGNALED(status))
	{
		if (is_last_stage)
			last_exit_status = 128 + WTERMSIG(status);
		job->num_processes_alive--;
	}
	else if (WIFSTOPPED(status))
	{
		job->status = STOPPED; // not used by tests, but fine to record
	}
	// Keep job in FOREGROUND until all pipeline children are reaped
	if (job->num_processes_alive == 0)
	{
		// Mark terminal state (EXIT vs SIGNAL)
		// not needed for the wait loop to end.
		if (WIFSIGNALED(status))
			job->status = TERMINATED_VIA_SIGNAL;
		else
			job->status = TERMINATED_VIA_EXIT;
	}
	else
	{
		// Ensure the waiter keeps waiting
		if (job->status == TERMINATED_VIA_EXIT
			|| job->status == TERMINATED_VIA_SIGNAL)
			job->status = FOREGROUND;
	}
}

/*
 * Run a program.
 *
 * A program's named children are various types of statements which
 * you can start implementing here.
 */
static void run_program(TSNode program)
{
    uint32_t n = ts_node_named_child_count(program);

    for (uint32_t i = 0; i < n; i++) {
        TSNode node = ts_node_named_child(program, i);
        const char *type = ts_node_type(node);

        /* VAR=VAL */
        if (strcmp(type, "variable_assignment") == 0) {
            TSNode name = ts_node_child_by_field_id(node, nameId);
            if (ts_node_is_null(name))
                name = ts_node_child_by_field_id(node, variableId);

            char *k = NULL, *v = NULL;
            if (!ts_node_is_null(name))
                k = ts_extract_node_text(input, name);

            TSNode val = ts_node_child_by_field_id(node, valueId);
            if (!ts_node_is_null(val)) v = expand_node_to_text(val);
            else v = strdup("");

            if (k) var_set(k, v);
            free(k);
            free(v);
            continue;
        }

        /* comments */
        if (strcmp(type, "comment") == 0) {
            continue;
        }

        /* redirs around command/pipeline */
        if (strcmp(type, "redirected_statement") == 0) {
            TSNode body = ts_node_child_by_field_id(node, bodyId);
            struct redir_spec r;
			// Pass the redirected_statement node
            collect_redirs(node, &r); 

            if (!ts_node_is_null(body)) {
                const char *bt = ts_node_type(body);

                if (strcmp(bt, "command") == 0) {
                    int argc = 0;
                    char **argv = build_argv_from_command(body, &argc);
                    if (argv && argv[0]) {
                        struct job *job = allocate_job(true);
                        job->status = FOREGROUND;
                        job->num_processes_alive = 1;
                        job->nprocs = 1;

                        pid_t pid;
                        if (spawn_stage(argv[0], argv, -1, -1, false, &r, 0,
                                         &pid, NULL, 0) == 0) {
                            job->pgid = pid;
                            job->pids[0] = pid;
                            wait_for_job(job);
                        }
                        delete_job(job, true);
                    }
                    if (argv) { for (int k = 0; k < argc; k++) free(argv[k]); free(argv); }
                } else if (strcmp(bt, "pipeline") == 0) {
                    execute_pipeline(body, &r);
                }
            }
            continue;
        }

        /* bare pipeline */
        if (strcmp(type, "pipeline") == 0) {
            execute_pipeline(node, NULL);
            continue;
        }

        /* bare command */
        if (strcmp(type, "command") == 0) {
            execute_command(node);
            continue;
        }

        /* list with && and || */
        if (strcmp(type, "list") == 0) {
            uint32_t nc = ts_node_child_count(node);
            for (uint32_t j = 0; j < nc; j++) {
                TSNode child = ts_node_child(node, j);
                if (!ts_node_is_named(child)) continue;

                const char *child_type = ts_node_type(child);

                if (strcmp(child_type, "command") == 0) {
                    execute_command(child);
                } else if (strcmp(child_type, "pipeline") == 0) {
                    execute_pipeline(child, NULL);
                } else if (strcmp(child_type, "redirected_statement") == 0) {
                    TSNode body = ts_node_child_by_field_id(child, bodyId);
                    struct redir_spec r2;
                    collect_redirs(child, &r2);
                    if (!ts_node_is_null(body)) {
                        const char *bt = ts_node_type(body);
                        if (strcmp(bt, "command") == 0) {
                            int argc = 0; char **argv = build_argv_from_command(body, &argc);
                            if (argv && argv[0]) {
                                struct job *job = allocate_job(true);
                                job->status = FOREGROUND;
                                job->num_processes_alive = 1;
                                job->nprocs = 1;
                                pid_t pid;
                                if (spawn_stage(argv[0], argv, -1, -1, false, &r2, 0,
                                                 &pid, NULL, 0) == 0) {
                                    job->pgid = pid;
                                    job->pids[0] = pid;
                                    wait_for_job(job);
                                }
                                delete_job(job, true);
                            }
                            if (argv) { for (int k = 0; k < argc; k++) free(argv[k]); free(argv); }
                        } else if (strcmp(bt, "pipeline") == 0) {
                            execute_pipeline(body, &r2);
                        }
                    }
                }

                /* handle && and || */
                if (j + 1 < nc) {
                    TSNode op_node = ts_node_child(node, j + 1);
                    if (!ts_node_is_named(op_node)) {
                        char *op = ts_extract_node_text(input, op_node);
                        if (op && strcmp(op, "&&") == 0) {
                            if (last_exit_status != 0) { j += 2; if (j < nc) j--; }
                        } else if (op && strcmp(op, "||") == 0) {
                            if (last_exit_status == 0) { j += 2; if (j < nc) j--; }
                        }
                        free(op);
                    }
                }
            }
            continue;
        }
	
		/* for ... do ... done */
if (strcmp(type, "for_statement") == 0) {
    TSNode varnode = ts_node_child_by_field_id(node, nameId);
    if (ts_node_is_null(varnode)) continue;
    char *varname = ts_extract_node_text(input, varnode);
    if (!varname) varname = strdup("");

    uint32_t nc = ts_node_named_child_count(node);
    TSNode body = ts_node_named_child(node, nc - 1);

    for (uint32_t i2 = 1; i2 + 1 < nc; i2++) {
        TSNode w = ts_node_named_child(node, i2);
        const char *wt = ts_node_type(w);
        if (!strcmp(wt, "word") || !strcmp(wt, "string") || !strcmp(wt, "raw_string") ||
            !strcmp(wt, "expansion") || !strcmp(wt, "simple_expansion") ||
            !strcmp(wt, "command_substitution")) {

            char *val = expand_node_to_text(w);
            var_set(varname, val ? val : "");
            free(val);

            loop_ctl = LOOP_NONE;
            const char *bt = ts_node_type(body);
            if (!strcmp(bt, "command"))       execute_command(body);
            else if (!strcmp(bt, "pipeline")) execute_pipeline(body, NULL);
            else if (!strcmp(bt, "list"))     run_program(body);

            if (loop_ctl == LOOP_BREAK)    { loop_ctl = LOOP_NONE; break; }
            if (loop_ctl == LOOP_CONTINUE) { loop_ctl = LOOP_NONE; continue; }
        }
    }
    free(varname);
    continue;
}

/* while ... do ... done */
if (strcmp(type, "while_statement") == 0) {
    TSNode cond = ts_node_named_child(node, 0);
    TSNode body = ts_node_named_child(node, 1);
    if (ts_node_is_null(cond) || ts_node_is_null(body)) continue;

    for (;;) {
        if (eval_condition_node(cond) != 0) break;

        loop_ctl = LOOP_NONE;
        const char *bt = ts_node_type(body);
        if (!strcmp(bt, "command"))       execute_command(body);
        else if (!strcmp(bt, "pipeline")) execute_pipeline(body, NULL);
        else if (!strcmp(bt, "list"))     run_program(body);

        if (loop_ctl == LOOP_BREAK)    { loop_ctl = LOOP_NONE; break; }
        if (loop_ctl == LOOP_CONTINUE) { loop_ctl = LOOP_NONE; continue; }
    }
    continue;
}





        /* if / then [/ else] */
/* if ... then ... [elif ... then ...]* [else ...] fi */
if (strcmp(type, "if_statement") == 0) {
    uint32_t nc = ts_node_named_child_count(node);
    if (nc < 2) { last_exit_status = 1; continue; }

    // IF
    TSNode cond = ts_node_named_child(node, 0);
    if (eval_condition_node(cond) == 0) {
        TSNode then_body = ts_node_named_child(node, 1);
        const char *bt = ts_node_type(then_body);
        if (!strcmp(bt, "command"))       execute_command(then_body);
        else if (!strcmp(bt, "pipeline")) execute_pipeline(then_body, NULL);
        else if (!strcmp(bt, "list"))     run_program(then_body);
        continue;
    }

    // ELIFs
    bool taken = false;
    for (uint32_t k = 2; k < nc; k++) {
        TSNode c = ts_node_named_child(node, k);
        const char *ct = ts_node_type(c);
        if (strcmp(ct, "elif_clause") != 0) break;

        TSNode ec_cond = ts_node_named_child(c, 0);
        if (eval_condition_node(ec_cond) == 0) {
            TSNode ec_body = ts_node_named_child(c, 1);
            const char *bt = ts_node_type(ec_body);
            if (!strcmp(bt, "command"))       execute_command(ec_body);
            else if (!strcmp(bt, "pipeline")) execute_pipeline(ec_body, NULL);
            else if (!strcmp(bt, "list"))     run_program(ec_body);
            taken = true;
            break;
        }
    }
    if (taken) continue;

    // ELSE
    TSNode last = ts_node_named_child(node, nc - 1);
    if (!ts_node_is_null(last) && !strcmp(ts_node_type(last), "else_clause")) {
        TSNode ebody = ts_node_named_child(last, 0);
        if (!ts_node_is_null(ebody)) {
            const char *bt = ts_node_type(ebody);
            if (!strcmp(bt, "command"))       execute_command(ebody);
            else if (!strcmp(bt, "pipeline")) execute_pipeline(ebody, NULL);
            else if (!strcmp(bt, "list"))     run_program(ebody);
        }
    }
    continue;
}


    }
}

/*
 * Read a script from this (already opened) file descriptor,
 * return a newly allocated buffer.
 */
static char	*read_script_from_fd(int readfd)
{
	struct stat	st;

	char		*userinput;

	ssize_t		off;

	ssize_t		n;

	size_t		cap;
	size_t		len;
	char		*buf;
	size_t		ncap;

	char		*nb;


	if (fstat(readfd, &st) != 0)
	{
		utils_error("Could not fstat input");
		return NULL;
	}
	// If it's a regular file, we can trust st_size; otherwise read until EOF.
	if (S_ISREG(st.st_mode))
	{
		userinput = malloc(st.st_size + 1);
		if (!userinput)
			return NULL;
		off = 0;
		while (off < st.st_size)
		{
			n = read(readfd, userinput + off, st.st_size - off);
			if (n < 0)
			{
				utils_error("Could not read input");
				free(userinput);
				return NULL;
			}
			if (n == 0)
				break ;
			off += n;
		}
		userinput[off] = 0;
		return userinput;
	}
	else
	{
		// Pipe, socket, tty: read in chunks
		cap = 4096;
		len = 0;
		buf = malloc(cap);
		if (!buf)
			return NULL;
		for (;;)
		{
			if (len + 2048 + 1 > cap)
			{
				ncap = cap * 2;
				nb = realloc(buf, ncap);
				if (!nb)
				{
					free(buf);
					return NULL;
				}
				cap = ncap;
				buf = nb;
			}
			n = read(readfd, buf + len, cap - len - 1);
			if (n < 0)
			{
				utils_error("Could not read input");
				free(buf);
				return NULL;
			}
			if (n == 0)
				break ;
			len += (size_t)n;
		}
		buf[len] = 0;
		return buf;
	}
}

/*
 * Execute the script whose content is provided in `script`
 */
static void	execute_script(char *script)
{
	TSTree	*tree;
	TSNode	program;

	input = script;
	tree = ts_parser_parse_string(parser, NULL, input, strlen(input));
	program = ts_tree_root_node(tree);
	signal_block(SIGCHLD);
	run_program(program);
	signal_unblock(SIGCHLD);
	ts_tree_delete(tree);
}

int	main(int ac, char *av[])
{
	int					opt;
	const TSLanguage	*bash = tree_sitter_bash();
	bool				shouldexit;
	char				*userinput;
	char				*prompt;
	int					readfd;

	tommy_hashdyn_init(&shell_vars);
	/* Process command-line arguments. See getopt(3) */
	while ((opt = getopt(ac, av, "h")) > 0)
	{
		switch (opt)
		{
		case 'h':
			usage(av[0]);
			break ;
		}
	}
	parser = ts_parser_new();
#define DEFINE_FIELD_ID(name) \
	name##Id = ts_language_field_id_for_name(bash, #name, strlen(#name))
	DEFINE_FIELD_ID(body);
	DEFINE_FIELD_ID(condition);
	DEFINE_FIELD_ID(name);
	DEFINE_FIELD_ID(right);
	DEFINE_FIELD_ID(left);
	DEFINE_FIELD_ID(operator);
	DEFINE_FIELD_ID(value);
	DEFINE_FIELD_ID(redirect);
	DEFINE_FIELD_ID(destination);
	DEFINE_FIELD_ID(variable);
	ts_parser_set_language(parser, bash);
	list_init(&job_list);
	signal_set_handler(SIGCHLD, sigchld_handler);
	/* Read/eval loop. */
	shouldexit = false;
	for (;;)
	{
		if (shouldexit)
			break ;
		/* If you fail this assertion, you were about to enter readline()
			* while SIGCHLD is blocked. This means that your shell would be
			* unable to receive SIGCHLD signals, and thus would be unable to
			* wait for background jobs that may finish while the
			* shell is sitting at the prompt waiting for user input.
			*/
		assert(!signal_is_blocked(SIGCHLD));
		userinput = NULL;
		/* Do not output a prompt unless shell's stdin is a terminal */
		if (isatty(0) && av[optind] == NULL)
		{
			prompt = isatty(0) ? build_prompt() : NULL;
			userinput = readline(prompt);
			free(prompt);
			if (userinput == NULL)
				break ;
		}
		else
		{
			readfd = 0;
			if (av[optind] != NULL)
				readfd = open(av[optind], O_RDONLY);
			userinput = read_script_from_fd(readfd);
			if (av[optind] != NULL)
				close(readfd);
			if (userinput == NULL)
				utils_fatal_error("Could not read input");
			shouldexit = true;
		}
		execute_script(userinput);
		free(userinput);
	}
	/*
		* Even though it is not necessary for the purposes of resource
		* reclamation, we free all allocated data structure prior to exiting
		* so that we can use valgrind's leak checker.
		*/
	ts_parser_delete(parser);
	tommy_hashdyn_foreach(&shell_vars, kv_free);
	tommy_hashdyn_done(&shell_vars);
	return EXIT_SUCCESS;
}
