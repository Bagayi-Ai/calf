use calf::calf::CALF;
use oracles::regex_oracle::RegexOracle;
use std::rc::Rc;

fn main() {
    let allowed_alphabets = vec!["a", "b"].into();
    let regex_oracle = RegexOracle::new("^b*(ab*)(ab*ab*)*$".to_string())
        .expect("Failed to create regex oracle");
    // running sample regex oracle
    let mut calf = CALF::new(Rc::new(allowed_alphabets), regex_oracle);

    calf.run();
    println!("done running regex oracle with CALF");
}
