use std::env;
use std::io;
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut stdin = io::stdin().lock();
    let mut stdout = io::stdout().lock();
    apollo_wasm::run_io(env::args(), &mut stdin, &mut stdout)
}
