use category_theory::core::errors::Errors;

#[derive(Debug)]
pub enum CalfErrors {
    UnknownError,
    MultipleMorphismsFromFSToPowerSet,
    MultipleMorphismsFromSuffixToPowerSet,
    MembershipQueryObjectNotFound,
    MultipleMorphismsFromFSToH
}

impl From<Errors> for CalfErrors {
    fn from(_: Errors) -> Self {
        CalfErrors::UnknownError
    }
}