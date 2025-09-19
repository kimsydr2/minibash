/*
 * minibash - an open-ended subset of bash
 *
 * Developed by Godmar Back for CS 3214 Fall 2025 
 * Virginia Tech.
 */
#define _GNU_SOURCE    1
#include <stdio.h>
#include <readline/readline.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <termios.h>
#include <sys/wait.h>
#include <assert.h>

#include <tree_sitter/api.h>
#include "tree_sitter/tree-sitter-bash.h"
#include "ts_symbols.h"
/* Since the handed out code contains a number of unused functions. */
#pragma GCC diagnostic ignored "-Wunused-function"

#include "hashtable.h"
#include "signal_support.h"
#include "utils.h"
#include "list.h"
#include "ts_helpers.h"
#include <spawn.h>
#include <sys/stat.h>

/* These are field ids suitable for use in ts_node_child_by_field_id for certain rules. 
   e.g., to obtain the body of a while loop, you can use:
    TSNode body = ts_node_child_by_field_id(child, bodyId);
*/
static TSFieldId bodyId, redirectId, destinationId, valueId, nameId, conditionId;
static TSFieldId variableId;
static TSFieldId leftId, operatorId, rightId;

static char *input;         // to avoid passing the current input around
static TSParser *parser;    // a singleton parser instance 
static tommy_hashdyn shell_vars;        // a hash table containing the internal shell variables

static void handle_child_status(pid_t pid, int status);
static char *read_script_from_fd(int readfd);
static void execute_script(char *script);

extern char **environ;
static void execute_command(TSNode command_node);
static int last_exit_status = 0;  // Track exit status of last command




static void
usage(char *progname)
{
    printf("Usage: %s -h\n"
        " -h            print this help\n",
        progname);

    exit(EXIT_SUCCESS);
}

/* Build a prompt */
static char *
build_prompt(void)
{
    return strdup("minibash> ");
}

/* Possible job status's to use.
 *
 * Some are specific to interactive job control which may not be needed
 * for this assignment.
 */
enum job_status {
    FOREGROUND,     /* job is running in foreground.  Only one job can be
                       in the foreground state. */
    BACKGROUND,     /* job is running in background */
    STOPPED,        /* job is stopped via SIGSTOP */
    NEEDSTERMINAL,  /* job is stopped because it was a background job
                       and requires exclusive terminal access */
    TERMINATED_VIA_EXIT,    /* job terminated via normal exit. */
    TERMINATED_VIA_SIGNAL   /* job terminated via signal. */
};

struct job {
    struct list_elem elem;   /* Link element for jobs list. */
    int     jid;             /* Job id. */
    enum job_status status;  /* Job status. */ 
    int  num_processes_alive;   /* The number of processes that we know to be alive */

    /* Add additional fields here as needed. */
};

/* Utility functions for job list management.
 * We use 2 data structures: 
 * (a) an array jid2job to quickly find a job based on its id
 * (b) a linked list to support iteration
 */
#define MAXJOBS (1<<16)
static struct list job_list;

static struct job *jid2job[MAXJOBS];

/* Return job corresponding to jid */
static struct job *
get_job_from_jid(int jid)
{
    if (jid > 0 && jid < MAXJOBS && jid2job[jid] != NULL)
        return jid2job[jid];

    return NULL;
}

/* Allocate a new job, optionally adding it to the job list. */
static struct job *
allocate_job(bool includeinjoblist)
{
    struct job * job = malloc(sizeof *job);
    job->num_processes_alive = 0;
    job->jid = -1;
    if (!includeinjoblist)
        return job;

    list_push_back(&job_list, &job->elem);
    for (int i = 1; i < MAXJOBS; i++) {
        if (jid2job[i] == NULL) {
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
static void
delete_job(struct job *job, bool removeFromJobList)
{
    if (removeFromJobList) {
        int jid = job->jid;
        assert(jid != -1);
        assert(jid2job[jid] == job);
        jid2job[jid]->jid = -1;
        jid2job[jid] = NULL;
    } else {
        assert(job->jid == -1);
    }
    /* add any other job cleanup here. */
    free(job);
}


/*
 * Suggested SIGCHLD handler.
 *
 * Call waitpid() to learn about any child processes that
 * have exited or changed status (been stopped, needed the
 * terminal, etc.)
 * Just record the information by updating the job list
 * data structures.  Since the call may be spurious (e.g.
 * an already pending SIGCHLD is delivered even though
 * a foreground process was already reaped), ignore when
 * waitpid returns -1.
 * Use a loop with WNOHANG since only a single SIGCHLD 
 * signal may be delivered for multiple children that have 
 * exited. All of them need to be reaped.
 */
static void
sigchld_handler(int sig, siginfo_t *info, void *_ctxt)
{
    pid_t child;
    int status;

    assert(sig == SIGCHLD);

    while ((child = waitpid(-1, &status, WUNTRACED|WNOHANG)) > 0) {
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
 * deallocated.  You should postpone deleting completed
 * jobs from the job list until when your code will no
 * longer touch them.
 *
 * The code below relies on `job->status` having been set to FOREGROUND
 * and `job->num_processes_alive` having been set to the number of
 * processes successfully forked for this job.
 */
static void
wait_for_job(struct job *job)
{
    assert(signal_is_blocked(SIGCHLD));

    while (job->status == FOREGROUND && job->num_processes_alive > 0) {
        int status;

        pid_t child = waitpid(-1, &status, WUNTRACED);

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


/**
 * Execute a simple command using posix_spawn.
 * Handles both absolute paths and PATH lookup.
 */
static void execute_command(TSNode command_node)
{
    TSNode name_node = ts_node_child_by_field_id(command_node, nameId);
    if (ts_node_is_null(name_node)) {
        name_node = ts_node_named_child(command_node, 0);
    }
    
    if (ts_node_is_null(name_node)) {
        fprintf(stderr, "Error: No command name found\n");
        return;
    }
    
    char *cmd_name = ts_extract_node_text(input, name_node);

    
    uint32_t child_count = ts_node_named_child_count(command_node);
    char **argv = calloc(child_count + 1, sizeof(char*));
    if (!argv) {
        fprintf(stderr, "Memory allocation failed\n");
        free(cmd_name);
        return;
    }
    
    argv[0] = cmd_name;
    int argv_index = 1;
    
    
    for (uint32_t i = 1; i < child_count; i++) {
        TSNode child = ts_node_named_child(command_node, i);
        const char *type = ts_node_type(child);
        
        
        char *arg_text = NULL;
        
        if (strcmp(type, "word") == 0) {
            arg_text = ts_extract_node_text(input, child);
        }
        else if (strcmp(type, "string") == 0) {
            uint32_t string_child_count = ts_node_child_count(child);
            for (uint32_t j = 0; j < string_child_count; j++) {
                TSNode string_child = ts_node_child(child, j);
                if (strcmp(ts_node_type(string_child), "string_content") == 0) {
                    arg_text = ts_extract_node_text(input, string_child);
                    break;
                }
            }
            if (arg_text == NULL) {
                arg_text = strdup(""); 
            }
        }
        else if (strcmp(type, "raw_string") == 0) {
            char *with_quotes = ts_extract_node_text(input, child);
            size_t len = strlen(with_quotes);
            if (len >= 2) {
                arg_text = strndup(with_quotes + 1, len - 2);
            } else {
                arg_text = strdup("");
            }
            free(with_quotes);
        }
        else if (strcmp(type, "number") == 0) {
            arg_text = ts_extract_node_text(input, child);
        }
else if (strcmp(type, "simple_expansion") == 0) {
    // Handle $? and other special variables
    // The structure: simple_expansion -> $ -> special_variable_name
    TSNode var_node = ts_node_child(child, 1);
    
    if (!ts_node_is_null(var_node)) {
        const char *var_type = ts_node_type(var_node);
        
        if (strcmp(var_type, "special_variable_name") == 0) {
            char *var_text = ts_extract_node_text(input, var_node);
            if (strcmp(var_text, "?") == 0) {
                arg_text = malloc(12);
                snprintf(arg_text, 12, "%d", last_exit_status);
            }
            free(var_text);
        }
    }
    if (arg_text == NULL) {
        arg_text = ts_extract_node_text(input, child);
    }
}
        if (arg_text != NULL) {
            argv[argv_index++] = arg_text;
        }
    } 
    
    argv[argv_index] = NULL;
    
    if (strcmp(cmd_name, "true") == 0) {
        last_exit_status = 0;
        for (int i = 0; i < argv_index; i++) {
            free(argv[i]);
        }
        free(argv);
        return;
    }
    if (strcmp(cmd_name, "false") == 0) {
        last_exit_status = 1;
        for (int i = 0; i < argv_index; i++) {
            free(argv[i]);
        }
        free(argv);
        return;
    }
    
    struct job *job = allocate_job(true);
    job->status = FOREGROUND;
    job->num_processes_alive = 1;
    
    pid_t pid;
    posix_spawnattr_t attr;
    posix_spawnattr_init(&attr);
    posix_spawnattr_setflags(&attr, POSIX_SPAWN_SETPGROUP);
    posix_spawnattr_setpgroup(&attr, 0);
    
    int spawn_result;
    if (cmd_name[0] == '/') {
        spawn_result = posix_spawn(&pid, cmd_name, NULL, &attr, argv, environ);
    } else {
        spawn_result = posix_spawnp(&pid, cmd_name, NULL, &attr, argv, environ);
    }
    
    posix_spawnattr_destroy(&attr);
    
    if (spawn_result != 0) {
        fprintf(stderr, "minibash: %s: command not found\n", cmd_name);
        last_exit_status = 127;
        job->status = TERMINATED_VIA_EXIT;
        job->num_processes_alive = 0;
        delete_job(job, true);
    } else {
        wait_for_job(job);
        delete_job(job, true);
    }
    
    for (int i = 0; i < argv_index; i++) {
        free(argv[i]);
    }
    free(argv);
} 

static void
handle_child_status(pid_t pid, int status)
{
    assert(signal_is_blocked(SIGCHLD));

    /* To be implemented. 
     * Step 1. Given the pid, determine which job this pid is a part of
     *         (how to do this is not part of the provided code.)
     * Step 2. Determine what status change occurred using the
     *         WIF*() macros.
     * Step 3. Update the job status accordingly, and adjust 
     *         num_processes_alive if appropriate.
     *         If a process was stopped, save the terminal state.
     */
    // todo 9/19:
    // 1. Find which job this pid belongs to
    // 2. Update that specific job's status
    // 3. Decrement num_processes_alive
    
    assert(signal_is_blocked(SIGCHLD));
    
    struct list_elem *e;
    for (e = list_begin(&job_list); e != list_end(&job_list); e = list_next(e)) {
        struct job *job = list_entry(e, struct job, elem);
        
        if (job->status == FOREGROUND) {
            if (WIFEXITED(status)) {
                last_exit_status = WEXITSTATUS(status);
                job->status = TERMINATED_VIA_EXIT;
                job->num_processes_alive--;
            } else if (WIFSIGNALED(status)) {
                last_exit_status = 128 + WTERMSIG(status);
                job->status = TERMINATED_VIA_SIGNAL;
                job->num_processes_alive--;
            } else if (WIFSTOPPED(status)) {
                job->status = STOPPED;
            }
            break;
        }
    }
}


/*
 * Run a program.
 *
 * A program's named children are various types of statements which 
 * you can start implementing here.
 */
static void 
run_program(TSNode program)
{
    uint32_t n = ts_node_named_child_count(program);
    for (uint32_t i = 0; i < n; i++) {
        TSNode child = ts_node_named_child(program, i);
        const char *type = ts_node_type(child);
        
        if (strcmp(type, "command") == 0) {
            execute_command(child);
        } else if (strcmp(type, "comment") == 0) {
            continue;
        } else {
            printf("node type `%s` not implemented\n", type);
        }
    }
}
/*
 * Read a script from this (already opened) file descriptor,
 * return a newly allocated buffer.
 */
static char *
read_script_from_fd(int readfd)
{
    struct stat st;
    if (fstat(readfd, &st) != 0) {
        utils_error("Could not fstat input");
        return NULL;
    }

    char *userinput = malloc(st.st_size+1);
    if (read(readfd, userinput, st.st_size) != st.st_size) {
        utils_error("Could not read input");
        free(userinput);
        return NULL;
    }
    userinput[st.st_size] = 0;
    return userinput;
}

/* 
 * Execute the script whose content is provided in `script`
 */
static void 
execute_script(char *script)
{
    input = script;
    TSTree *tree = ts_parser_parse_string(parser, NULL, input, strlen(input));
    TSNode  program = ts_tree_root_node(tree);
    signal_block(SIGCHLD);
    run_program(program);
    signal_unblock(SIGCHLD);
    ts_tree_delete(tree);
}

int
main(int ac, char *av[])
{
    int opt;
    tommy_hashdyn_init(&shell_vars);

    /* Process command-line arguments. See getopt(3) */
    while ((opt = getopt(ac, av, "h")) > 0) {
        switch (opt) {
        case 'h':
            usage(av[0]);
            break;
        }
    }

    parser = ts_parser_new();
    const TSLanguage *bash = tree_sitter_bash();
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
    bool shouldexit = false;
    for (;;) {
        if (shouldexit)
            break;

        /* If you fail this assertion, you were about to enter readline()
         * while SIGCHLD is blocked.  This means that your shell would be
         * unable to receive SIGCHLD signals, and thus would be unable to
         * wait for background jobs that may finish while the
         * shell is sitting at the prompt waiting for user input.
         */
        assert(!signal_is_blocked(SIGCHLD));

        char *userinput = NULL;
        /* Do not output a prompt unless shell's stdin is a terminal */
        if (isatty(0) && av[optind] == NULL) {
            char *prompt = isatty(0) ? build_prompt() : NULL;
            userinput = readline(prompt);
            free (prompt);
            if (userinput == NULL)
                break;
        } else {
            int readfd = 0;
            if (av[optind] != NULL)
                readfd = open(av[optind], O_RDONLY);

            userinput = read_script_from_fd(readfd);
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
    tommy_hashdyn_foreach(&shell_vars, hash_free);
    tommy_hashdyn_done(&shell_vars);
    return EXIT_SUCCESS;
}

