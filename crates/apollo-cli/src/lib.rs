use std::io::Write;
use std::process::ExitCode;

pub fn run<I, S, W, E>(args: I, out: &mut W, err: &mut E) -> ExitCode
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
    W: Write,
    E: Write,
{
    let mut iter = args.into_iter();
    let _program = iter.next();
    match iter.next().as_ref().map(AsRef::as_ref) {
        None | Some("--help" | "-h" | "help") => {
            let _ = writeln!(out, "apollo {}", apollo_kernel::version());
            ExitCode::SUCCESS
        }
        Some("--version" | "-V" | "version") => {
            let _ = writeln!(out, "{}", apollo_kernel::version());
            ExitCode::SUCCESS
        }
        Some(other) => {
            let _ = writeln!(err, "unknown command: {other}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use std::process::ExitCode;

    use super::run;

    #[test]
    fn help_prints_banner_and_succeeds() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let code = run(["apollo", "--help"], &mut out, &mut err);
        assert_eq!(code, ExitCode::SUCCESS);
        assert_eq!(String::from_utf8_lossy(&out), "apollo 0.1.0\n");
        assert_eq!(String::from_utf8_lossy(&err), "");
    }

    #[test]
    fn version_prints_kernel_version() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let code = run(["apollo", "--version"], &mut out, &mut err);
        assert_eq!(code, ExitCode::SUCCESS);
        assert_eq!(String::from_utf8_lossy(&out), "0.1.0\n");
        assert_eq!(String::from_utf8_lossy(&err), "");
    }

    #[test]
    fn unknown_command_fails() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let code = run(["apollo", "nope"], &mut out, &mut err);
        assert_eq!(code, ExitCode::FAILURE);
        assert_eq!(String::from_utf8_lossy(&out), "");
        assert_eq!(String::from_utf8_lossy(&err), "unknown command: nope\n");
    }
}
