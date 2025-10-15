use std::hash::Hash;
use std::sync::Arc;
use calf::calf::CALF;
use oracles::regex_oracle::RegexOracle;
use std::rc::Rc;
use category_theory::core::base_category::BaseCategory;
use category_theory::core::discrete_category::DiscreteCategory;
use category_theory::core::dynamic_category::DynamicCategory;
use category_theory::core::object_id::ObjectId;
use category_theory::core::persistable_category::PersistableCategory;
use category_theory::core::traits::category_trait::{CategoryTrait, CategoryFromObjects, CategoryCloneWithNewId};


#[tokio::main]
async fn main() {
    category_theory::init_db(Some("calf")).await.unwrap();
    run::<PersistableCategory<DynamicCategory>>().await;
    // run::<DiscreteCategory>().await;
    // run::<DiscreteCategory>().await;
}


async fn run<Category>()
where
    Category: CategoryTrait + Hash + Eq + Clone + From<String> + CategoryCloneWithNewId,
    Category::Object: Clone + for<'a> From<&'a str> + From<String>,
    <Category::Object as CategoryTrait>::Object: Clone + for<'a> From<&'a str> + From<String> + From<ObjectId>,
{
    let allowed_alphabets = Category::from_objects(vec!["a", "b"]).await.unwrap();
    let regex_oracle = RegexOracle::new("^b*(ab*)(ab*ab*)*$".to_string())
        .expect("Failed to create regex oracle");
    // running sample regex oracle
    let mut calf: CALF<RegexOracle, BaseCategory<Category>> = CALF::new(allowed_alphabets.into(), regex_oracle).await;

    calf.run().await.unwrap();

    calf.export_cytoscape("/Users/mwas/projects/CALFrs/main_regex_oracle.json").await.unwrap();

    println!("done running regex oracle with CALF");
}
