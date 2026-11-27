use std::io;
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut out = io::stdout().lock();
    let mut err = io::stderr().lock();
    apollo_cli::run(std::env::args(), &mut out, &mut err)
}
