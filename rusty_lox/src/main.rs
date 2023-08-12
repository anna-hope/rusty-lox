use rlox_lib::{
    chunk::{Chunk, OpCode},
    vm::VM,
};

fn main() {
    let mut chunk = Chunk::new();
    let index = chunk.add_constant(1.2);
    chunk.add_code(OpCode::Constant(index), 123);

    let index = chunk.add_constant(3.4);
    chunk.add_code(OpCode::Constant(index), 123);

    chunk.add_code(OpCode::Add, 123);

    let index = chunk.add_constant(5.6);
    chunk.add_code(OpCode::Constant(index), 123);

    chunk.add_code(OpCode::Divide, 123);
    chunk.add_code(OpCode::Negate, 123);

    chunk.add_code(OpCode::Return, 123);

    chunk.disassemble("test chunk");
    println!();

    let mut vm = VM::new();
    vm.interpret(&chunk);
}
