
How to build minibash
---------------------

1. Build libtommy
```
(cd tommyds; make)
```

2. Build libtree-sitter.a
```
(cd tree-sitter; make)
```

3. Build minibash

```
cd src
make
```

4. To use the tree-sitter CLI tool, it is recommended to
```
source env.sh
```

4. Test with
```
tree-sitter parse tests/001-comment.sh
```
(The `tree-sitter` example must be separately installed; ours is in
`~cs3214/bin`)
