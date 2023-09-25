use std::fs;
use std::io;
use std::io::Write;
use std::process::ExitCode;

use rlox_lib::vm::{InterpretError, Result, Vm};

fn main() -> ExitCode {
    let mut vm = Vm::new();

    let args = std::env::args().collect::<Vec<_>>();
    match args.len() {
        1 => {
            repl(&mut vm);
            ExitCode::SUCCESS
        }
        2 => match run_file(args[1].clone(), &mut vm) {
            Ok(_) => ExitCode::SUCCESS,
            Err(error) => match error {
                InterpretError::Compile(_) => ExitCode::from(65),
                InterpretError::Runtime(msg) => {
                    eprintln!("{msg}");
                    ExitCode::from(70)
                }
            },
        },
        _ => {
            eprintln!("Usage: rlox [path]");
            ExitCode::from(64)
        }
    }
}

fn repl(vm: &mut Vm) {
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

        if let Ok(value) = vm.interpret(buffer) {
            println!("{value}");
        }
    }
}

fn run_file(path: String, vm: &mut Vm) -> Result<()> {
    let source = fs::read_to_string(path).expect("Should be able to read the file");
    let value = vm.interpret(source)?;
    println!("{value}");
    Ok(())
}
