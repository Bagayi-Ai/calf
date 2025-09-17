use calf::calf::CALF;
use oracles::regex_oracle::RegexOracle;
use std::rc::Rc;
use category_theory::core::base_category::BaseCategory;
use category_theory::core::discrete_category::DiscreteCategory;
use category_theory::core::dynamic_category::DynamicCategory;

fn main() {
    let allowed_alphabets: DiscreteCategory = vec!["a", "b"].into();
    let regex_oracle = RegexOracle::new("^b*(ab*)(ab*ab*)*$".to_string())
        .expect("Failed to create regex oracle");
    // running sample regex oracle
    let mut calf: CALF<RegexOracle, BaseCategory<DiscreteCategory>> = CALF::new(allowed_alphabets.into(), regex_oracle);

    calf.run().unwrap();
    println!("done running regex oracle with CALF");
    // let allowed_alphabets: DynamicCategory = vec!["a", "b"].into();
    // let regex_oracle = RegexOracle::new("^b*(ab*)(ab*ab*)*$".to_string())
    //     .expect("Failed to create regex oracle");
    // // running sample regex oracle
    // let mut calf: CALF<RegexOracle, DynamicCategory> = CALF::new(allowed_alphabets.into(), regex_oracle);
    // 
    // calf.run().unwrap();
    // println!("done running regex oracle with CALF");
}


fn using_discrete(){
    let allowed_alphabets: DiscreteCategory = vec!["a", "b"].into();
    let regex_oracle = RegexOracle::new("^b*(ab*)(ab*ab*)*$".to_string())
        .expect("Failed to create regex oracle");
    // running sample regex oracle
    let mut calf: CALF<RegexOracle, BaseCategory<DiscreteCategory>> = CALF::new(allowed_alphabets.into(), regex_oracle);

    calf.run().unwrap();
    println!("done running regex oracle with CALF");
}
