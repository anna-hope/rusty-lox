use mimalloc::MiMalloc;

mod chunk;
mod compiler;
mod scanner;
mod value;
pub mod vm;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

#[cfg(test)]
mod tests {}
