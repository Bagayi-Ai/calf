use regex::Regex;
use calf::oracle_trait::{AutomatonTrait, OracleTrait};
use crate::oracle_error::OracleError;

pub struct RegexOracle {
    regex: Regex,
}



impl RegexOracle {
    /// Creates a new `RegexOracle` with the given regex pattern.
    pub fn new(regex_string: String) -> Result<Self, OracleError> {
        match Regex::new(&regex_string) {
            Ok(regex) => Ok(RegexOracle { regex }),
            Err(_) => Err(OracleError::InvalidRegexPattern(regex_string)),
        }
    }

    /// Checks if the input string matches the regex pattern.
    pub fn matches(&self, input: &str) -> bool {
        self.regex.is_match(input)
    }
}


impl OracleTrait<String> for RegexOracle {
    fn membership_query(&self, input: &String) -> bool {
        self.matches(input)
    }

    fn equivalence_query<H: AutomatonTrait<String>>(&self, hypothesis: &H) -> Option<String> {
        todo!()
    }
}