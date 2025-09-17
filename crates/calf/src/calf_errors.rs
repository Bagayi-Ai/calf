use category_theory::core::errors::Errors;

#[derive(Debug)]
pub enum CalfErrors {
    UnknownError,
    MultipleMorphismsFromFSToPowerSet,
    MultipleMorphismsFromFHtoPowerset,
    MultipleMorphismsFromFStoFH,
    MultipleMorphismsFromSuffixToPowerSet,
    MembershipQueryObjectNotFound,
    MultipleMorphismsFromFSToH,
    NoMorphismFromFStoFH,
    InvalidMappingFromFStoFH,
    InvalidMappingFromFHtoPowerset,
    InvalidMappingFromHtoPowerset,
    MultipleMorphismsFromFStoH,
    MultipleMorphismsFromFHtoH
}

impl From<Errors> for CalfErrors {
    fn from(_: Errors) -> Self {
        CalfErrors::UnknownError
    }
}