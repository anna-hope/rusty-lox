# rusty-lox

A work-in-progress interpreter for the Lox language from [Crafting Interpreters](https://craftinginterpreters.com),
implemented in Rust.

**Warning:** this is a GC-based branch of the interpreter, which can be up to 3x slower than
the main (reference counting-based) branch.

## Running

### REPL

`cargo run --release`

### Script

`cargo run --release [path_to_script.lox]`

## Printing the bytecode

If you need to see the emitted bytecode as it is being executed
(e.g. for debugging purposes), set the following environment variables:

- DEBUG_PRINT_CODE=1

