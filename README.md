# Tygr

Tygr is a small, statically-typed functional programming language with an interpreter written in Rust. It features a
robust type system based on Hindley-Milner type inference, supporting modern functional programming paradigms.

## Features

### Type System

Tygr implements an extended version of Algorithm W. Type annotations are optional but fully supported.

Here are some key constructs:

- ADTs (variants): Define custom tagged unions with generic type parameters.
    ```ml
    enum Option[t] =
    | Some(t)
    | None
    ```
- Pattern matching on variants, lists, and records
- Parametric polymorphism on functions and data types
- Higher-kinded types: Includes kind inference to ensure type constructors are well-formed.
- Lists, fixed-field records, tuples, and standard primitive types (`float`, `int`, etc.)

Additionally, we support recursion through recursive records and `let rec` syntax (internally desugared to recursive
records).

## Getting Started

### Prerequisites

* [Rust](https://www.rust-lang.org/tools/install) (Cargo)

### Installation

Clone the repository and build the project using Cargo:

```bash
git clone https://github.com/benaepli/tygr.git
cd tygr
cargo build --release
```

### Running Programs

You can interpret Tygr source files directly using `cargo run`.

```bash
cargo run -- examples/scripts/reduce.tygr
```

Running without any input arguments will launch a REPL:

```bash
cargo run
```

## Examples

You can find example programs demonstrating recursion, pattern matching, and type definitions in the `examples`
directory.

Here are a couple:

* [examples/scripts/reduce.tygr](examples/scripts/reduce.tygr): Demonstrates list processing (`fold_left`/`fold_right`)
  and recursion.
* [examples/scripts/mutual.tygr](examples/scripts/mutual.tygr): Demonstrates mutual recursion using
  recursive records.
* [examples/scripts/calculator.tygr](examples/scripts/calculator.tygr): A simple calculator using recursive variants.

## Documentation

For a formal specification of the language syntax, please refer to
the [EBNF Specification](docs/ebnf.md).