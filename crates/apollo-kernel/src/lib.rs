pub mod level;
pub mod multiplicity;
pub mod nbe;
pub mod term;

pub use level::{Level, LevelVar};
pub use multiplicity::{Multiplicity, UsageError, UsageVec};
pub use nbe::{Closure, Env, EvalError, Neutral, Value};
pub use term::{DeBruijnLevel, Index, Term, TermArena, TermId};

#[must_use]
pub const fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

#[cfg(test)]
mod tests {
    use super::version;

    #[test]
    fn reports_package_version() {
        assert_eq!(version(), env!("CARGO_PKG_VERSION"));
    }
}
