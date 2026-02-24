#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("input not in prime subgroup")]
    InvalidSubgroup,
    #[error("delta must be non-zero")]
    ZeroDelta,
    #[error("rho must be non-zero")]
    ZeroRho,
    #[error("mismatched vector sizes")]
    MismatchedSizes,
    #[error("public input length mismatch: expected {expected}, got {actual}")]
    PublicInputLength { expected: usize, actual: usize },
    #[error("instance commitment IC(x) is zero")]
    ZeroInstanceCommitment,
    #[error("target R is degenerate (zero or one)")]
    DegenerateTarget,
    #[error("no symbolic pairing products available")]
    NoSymbolicProducts,
    #[error("symbolic linear system is inconsistent")]
    SymbolicSystemInconsistent,
}

pub type Result<T> = core::result::Result<T, Error>;
