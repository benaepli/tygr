# Design

TODO write about:

- fix operator: for recursion
- equality: only compare basic types
- parsed AST -> typed AST conversion that performs:
    - desugaring
    - type-checking
    - closures (and closure optimization)

## AST Design

In the top-level, we parse to a list of declarations.
Everything at the top-level is a declaration, not an expression.
A declaration contains two fields:

1. The name.
2. The value.

This allows us the AST representation to be quite nice. Conceptually, the user types:

```
let x = 5
let f = fn y => y + 1
let answer = f x
```

which gets desugared to:

```
let x = 5 in
let f = fn y => y + 1 in
let answer = f x in
answer
```

This is a single expression. We always return the result of the last declaration,
and we always require at least one declaration in the program.

## Recursion

Typically, this de-sugaring might be a problem for mutual recursion. However, my language does
not allow for typical recursion at all. We instead use a `fix` operator:

```
let factorial = fix(fn self => fn n => if n == 0 then 1 else n * self(n - 1))
```