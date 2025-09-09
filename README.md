
How to build minibash
---------------------

1. Build libtommy
```
(cd tommyds; make)
```

2. Build minibash

```
cd src
make
```

3. To use the tree-sitter CLI tool, it is recommended to 
```
source env.sh
```

4. Test with
```
tree-sitter parse tests/001-comment.sh
```
(The `tree-sitter` example must be separately installed; ours is in
`~cs3214/bin`)
