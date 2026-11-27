use std::process::ExitCode;

fn main() -> ExitCode {
    let _ = std::env::args().count();
    ExitCode::SUCCESS
}
