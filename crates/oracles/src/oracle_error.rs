

#[derive(Debug)]
pub enum OracleError {
    InvalidRegexPattern(String),
    MembershipQueryFailed(String),
    EquivalenceQueryFailed(String),
    UnknownError,
}