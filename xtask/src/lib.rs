pub mod ste100;

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Task {
    Check,
    PreCommit,
    Fmt,
    Clippy,
    Test,
    Cov,
    Deny,
    Machete,
    Ste100,
    InstallHooks,
    Help,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommandSpec {
    pub program: String,
    pub args: Vec<String>,
}

impl CommandSpec {
    #[must_use]
    pub fn new(program: &str, args: &[&str]) -> Self {
        Self {
            program: program.to_owned(),
            args: args.iter().map(|arg| (*arg).to_owned()).collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Step {
    Command(CommandSpec),
    Ste100,
}

pub fn parse_task(arg: Option<&str>) -> Result<Task, String> {
    match arg {
        None | Some("--help" | "-h" | "help") => Ok(Task::Help),
        Some("check") => Ok(Task::Check),
        Some("pre-commit") => Ok(Task::PreCommit),
        Some("fmt") => Ok(Task::Fmt),
        Some("clippy") => Ok(Task::Clippy),
        Some("test") => Ok(Task::Test),
        Some("cov") => Ok(Task::Cov),
        Some("deny") => Ok(Task::Deny),
        Some("machete") => Ok(Task::Machete),
        Some("ste100") => Ok(Task::Ste100),
        Some("install-hooks") => Ok(Task::InstallHooks),
        Some(other) => Err(format!("unknown xtask command: {other}")),
    }
}

#[must_use]
pub fn plan(task: Task) -> Vec<Step> {
    match task {
        Task::Help => Vec::new(),
        Task::Fmt => vec![Step::Command(CommandSpec::new(
            "cargo",
            &["fmt", "--all", "--", "--check"],
        ))],
        Task::Clippy => vec![Step::Command(CommandSpec::new(
            "cargo",
            &[
                "clippy",
                "--workspace",
                "--all-targets",
                "--",
                "-D",
                "warnings",
            ],
        ))],
        Task::Test => vec![Step::Command(CommandSpec::new(
            "cargo",
            &["nextest", "run", "--workspace"],
        ))],
        Task::Cov => vec![Step::Command(CommandSpec::new(
            "cargo",
            &[
                "llvm-cov",
                "--workspace",
                "--summary-only",
                "--fail-under-lines",
                "90",
            ],
        ))],
        Task::Deny => vec![Step::Command(CommandSpec::new(
            "cargo",
            &["deny", "check", "bans", "licenses", "sources"],
        ))],
        Task::Machete => vec![Step::Command(CommandSpec::new("cargo-machete", &[]))],
        Task::Ste100 => vec![Step::Ste100],
        Task::InstallHooks => vec![Step::Command(CommandSpec::new(
            "git",
            &["config", "core.hooksPath", ".githooks"],
        ))],
        Task::PreCommit => [Task::Fmt, Task::Clippy, Task::Ste100]
            .into_iter()
            .flat_map(plan)
            .collect(),
        Task::Check => [
            Task::Fmt,
            Task::Clippy,
            Task::Test,
            Task::Cov,
            Task::Deny,
            Task::Machete,
            Task::Ste100,
        ]
        .into_iter()
        .flat_map(plan)
        .collect(),
    }
}

#[must_use]
pub fn workspace_root() -> PathBuf {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest_dir.parent().unwrap_or(manifest_dir).to_path_buf()
}

pub fn run<I, S, W, E, F>(args: I, root: &Path, out: &mut W, err: &mut E, mut exec: F) -> ExitCode
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
    W: Write,
    E: Write,
    F: FnMut(&CommandSpec, &Path) -> Result<(), String>,
{
    let mut iter = args.into_iter();
    let _program = iter.next();
    let task = match parse_task(iter.next().as_ref().map(AsRef::as_ref)) {
        Ok(task) => task,
        Err(message) => {
            let _ = writeln!(err, "{message}");
            return ExitCode::FAILURE;
        }
    };

    if task == Task::Help {
        let _ = writeln!(
            out,
            "tasks: check, pre-commit, fmt, clippy, test, cov, deny, machete, ste100, install-hooks"
        );
        return ExitCode::SUCCESS;
    }

    for step in plan(task) {
        match step {
            Step::Command(spec) => {
                if let Err(message) = exec(&spec, root) {
                    let _ = writeln!(err, "{message}");
                    return ExitCode::FAILURE;
                }
            }
            Step::Ste100 => match ste100::check_root(root) {
                Ok(violations) if violations.is_empty() => {
                    let _ = writeln!(out, "ste100 ok");
                }
                Ok(violations) => {
                    for violation in violations {
                        let _ = writeln!(err, "{violation}");
                    }
                    return ExitCode::FAILURE;
                }
                Err(io_err) => {
                    let _ = writeln!(err, "ste100 io error: {io_err}");
                    return ExitCode::FAILURE;
                }
            },
        }
    }

    ExitCode::SUCCESS
}

pub fn run_system_command(spec: &CommandSpec, root: &Path) -> Result<(), String> {
    let status = Command::new(&spec.program)
        .args(&spec.args)
        .current_dir(root)
        .status()
        .map_err(|io_err| format!("failed to start {}: {io_err}", spec.program))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!(
            "command failed: {} {}",
            spec.program,
            spec.args.join(" ")
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::process::ExitCode;

    use super::{CommandSpec, Step, Task, parse_task, plan, run, workspace_root};

    #[test]
    fn parses_all_tasks() {
        assert_eq!(parse_task(None), Ok(Task::Help));
        assert_eq!(parse_task(Some("check")), Ok(Task::Check));
        assert_eq!(parse_task(Some("pre-commit")), Ok(Task::PreCommit));
        assert_eq!(parse_task(Some("fmt")), Ok(Task::Fmt));
        assert_eq!(parse_task(Some("clippy")), Ok(Task::Clippy));
        assert_eq!(parse_task(Some("test")), Ok(Task::Test));
        assert_eq!(parse_task(Some("cov")), Ok(Task::Cov));
        assert_eq!(parse_task(Some("deny")), Ok(Task::Deny));
        assert_eq!(parse_task(Some("machete")), Ok(Task::Machete));
        assert_eq!(parse_task(Some("ste100")), Ok(Task::Ste100));
        assert_eq!(parse_task(Some("install-hooks")), Ok(Task::InstallHooks));
        assert!(parse_task(Some("bogus")).is_err());
    }

    #[test]
    fn check_plan_contains_all_gates() {
        let steps = plan(Task::Check);
        assert_eq!(steps.len(), 7);
        assert_eq!(steps.last(), Some(&Step::Ste100));
        assert_eq!(plan(Task::Help), Vec::new());
        assert_eq!(plan(Task::PreCommit).len(), 3);
        assert_eq!(plan(Task::InstallHooks).len(), 1);
    }

    #[test]
    fn run_executes_planned_steps_and_ste100() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let mut executed = Vec::new();
        let root = workspace_root();

        let code = run(
            ["xtask", "pre-commit"],
            &root,
            &mut out,
            &mut err,
            |spec: &CommandSpec, _dir: &Path| {
                executed.push(spec.clone());
                Ok(())
            },
        );

        assert_eq!(code, ExitCode::SUCCESS);
        assert_eq!(executed.len(), 2);
        assert_eq!(String::from_utf8_lossy(&out), "ste100 ok\n");
        assert_eq!(String::from_utf8_lossy(&err), "");
    }

    #[test]
    fn run_reports_ste100_violations() {
        let dir = std::env::temp_dir().join(format!("apollo-xtask-test-{}", std::process::id()));
        let docs = dir.join("docs").join("nested");
        assert!(std::fs::create_dir_all(&docs).is_ok());
        assert!(std::fs::write(docs.join("bad.md"), "Do not utilize this.").is_ok());

        let mut out = Vec::new();
        let mut err = Vec::new();
        let code = run(["xtask", "ste100"], &dir, &mut out, &mut err, |_, _| Ok(()));
        let _ = std::fs::remove_dir_all(&dir);

        assert_eq!(code, ExitCode::FAILURE);
        assert_eq!(String::from_utf8_lossy(&out), "");
        assert!(String::from_utf8_lossy(&err).contains("utilize"));
    }

    #[test]
    fn run_prints_help_and_handles_failures() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let root = workspace_root();

        assert_eq!(
            run(["xtask", "help"], &root, &mut out, &mut err, |_, _| Ok(())),
            ExitCode::SUCCESS
        );
        assert!(String::from_utf8_lossy(&out).contains("ste100"));

        let fail_code = run(["xtask", "fmt"], &root, &mut out, &mut err, |_, _| {
            Err("fmt failed".to_owned())
        });
        assert_eq!(fail_code, ExitCode::FAILURE);
        assert!(String::from_utf8_lossy(&err).contains("fmt failed"));

        let unknown_code = run(["xtask", "unknown"], &root, &mut out, &mut err, |_, _| {
            Ok(())
        });
        assert_eq!(unknown_code, ExitCode::FAILURE);
    }

    #[test]
    fn run_system_command_handles_success_failure_and_missing_binary() {
        let root = workspace_root();
        let ok = super::run_system_command(&CommandSpec::new("cargo", &["--version"]), &root);
        assert!(ok.is_ok());

        let fail = super::run_system_command(
            &CommandSpec::new("cargo", &["definitely-invalid-subcommand-xyz"]),
            &root,
        );
        assert!(fail.is_err());

        let missing = super::run_system_command(
            &CommandSpec::new("apollo-definitely-missing-binary-xyz", &[]),
            &root,
        );
        assert!(missing.is_err());
    }
}
