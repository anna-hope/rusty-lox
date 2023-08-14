use std::fs;
use std::io;
use std::io::Write;
use std::process::ExitCode;

use rlox_lib::vm::{InterpretError, Result, VM};

fn main() -> ExitCode {
    let vm = VM::new();

    let args = std::env::args().collect::<Vec<_>>();
    match args.len() {
        1 => {
            repl(&vm);
            ExitCode::SUCCESS
        }
        2 => match run_file(args[1].clone(), &vm) {
            Ok(_) => ExitCode::SUCCESS,
            Err(error) => match error {
                InterpretError::Compile => ExitCode::from(65),
                InterpretError::Runtime => ExitCode::from(70),
            },
        },
        _ => {
            eprintln!("Usage: rlox [path]");
            ExitCode::from(64)
        }
    }
}

fn repl(vm: &VM) {
    loop {
        print!("> ");
        io::stdout().flush().expect("Should flush stdout");

        let mut buffer = String::new();
        io::stdin()
            .read_line(&mut buffer)
            .expect("Should be able to read line");

        if buffer.is_empty() {
            println!();
            break;
        }

        let _ = vm.interpret(buffer);
    }
}

fn run_file(path: String, vm: &VM) -> Result<()> {
    let source = fs::read_to_string(path).expect("Should be able to read the file");
    vm.interpret(source)
}
