use std::io;
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut out = io::stdout().lock();
    let mut err = io::stderr().lock();
    let root = xtask::workspace_root();
    xtask::run(
        std::env::args(),
        &root,
        &mut out,
        &mut err,
        xtask::run_system_command,
    )
}
