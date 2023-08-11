use rlox_lib::chunk::{Chunk, OpCode};

fn main() {
    let mut chunk = Chunk::new();
    let constant = chunk.add_constant(1.2);

    chunk.add_code(OpCode::OpConstant(constant), 123);
    chunk.add_code(OpCode::OpReturn, 123);

    chunk.disassemble("test chunk");
}
