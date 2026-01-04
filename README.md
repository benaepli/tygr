# Tygr

Tygr is a statically-typed functional programming language. It features a
robust type system with higher-kinded types based on Hindley-Milner type inference.

In addition to the core language, it supports a Rust-like module system, strong error reporting, as well as a REPL
that runs in WASM (on my website!).

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

Tygr provides a CLI with several subcommands to run and inspect your code.

#### REPL

Start the interactive Read-Eval-Print Loop (REPL) by running:

```bash
cargo run -- repl
# opr simply
cargo run
```

#### Scripts

Run a standalone Tygr script (a file containing a sequence of statements) using the `script` subcommand:

```bash
cargo run -- script examples/scripts/factorial.tygr
```

#### Projects & Binaries

To run a full Tygr project (defined by a `Tygr.toml` manifest) or a standalone program file (requiring a `main`
function):

**Run the project in the current directory:**

```bash
cargo run -- run
```

**Run a specific standalone program file:**

```bash
cargo run -- run --file examples/crates/basic_binary/src/main.tygr
```

#### Visualization

You can visualize the intermediate representations (IR) of the compiler:

```bash
# Visualize the Typed AST
cargo run -- visualize typed examples/programs/bst.tygr
cargo run -- visualize closure examples/programs/bst.tygr
cargo run -- visualize constructor examples/programs/bst.tygr
```

## Project System

Tygr supports a crate-based project system similar to Rust's. A project is defined by a `Tygr.toml` manifest file.

### Manifest (`Tygr.toml`)

```toml
[project]
name = "my_project"
type = "binary" # or "lib"

[dependencies]
# Map an alias to a local path
my_lib = "../path/to/my_lib"
```

### Directory Structure

- **Binary Projects**: Source code entry point is `src/main.tygr`.
- **Library Projects**: Source code entry point is `src/lib.tygr`.

Example structure:

```text
my_project/
├── Tygr.toml
└── src/
    └── main.tygr
```

## Examples

You can find example programs demonstrating recursion, pattern matching, and type definitions in the `examples`
directory.

Here are some scripts:

* [examples/scripts/reduce.tygr](examples/scripts/reduce.tygr): Demonstrates list processing (`fold_left`/`fold_right`)
  and recursion.
* [examples/scripts/mutual.tygr](examples/scripts/mutual.tygr): Demonstrates mutual recursion using
  recursive records.
* [examples/scripts/calculator.tygr](examples/scripts/calculator.tygr): A simple calculator using recursive variants.

To see examples of the module system, see [examples/crates](examples/crates).

## Documentation

For a formal specification of the language syntax, please refer to
the [EBNF Specification](docs/ebnf.md).