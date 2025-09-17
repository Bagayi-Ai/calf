use std::hash::Hash;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use uuid::Uuid;
use category_theory::core::traits::category_trait::{CategorySubObjectAlias, CategoryTrait, MorphismCommutationResult};
use category_theory::core::arrow::{Morphism, Functor, Arrow};
use category_theory::core::product_endofunctor::apply_product;
use category_theory::core::traits::arrow_trait::ArrowTrait;
use category_theory::core::epic_monic_category::EpicMonicCategory;
use category_theory::core::expand_functor::expand_functor;
use category_theory::core::traits::factorization_system_trait::FactorizationSystemTrait;
use crate::calf_errors::CalfErrors;
use crate::oracle_trait::{OracleTrait, QueryInputTrait};


enum Closed<Category: CategoryTrait> {
    Closed,
    NotClosed(HashSet<Rc<Category::Morphism>>),
}


enum Consistent<Category: CategoryTrait> {
    Consistent,
    NotConsistent(HashSet<Rc<Category::Morphism>>),
}


pub struct CALF<
    Oracle: OracleTrait<String>,
    BaseCategory: CategoryTrait + Hash + Eq + Clone
>
where
    <BaseCategory as CategoryTrait>::Object: Clone + From<String>,
    <<BaseCategory as CategoryTrait>::Object as CategoryTrait>::Object: Clone,
{
    category: EpicMonicCategory<BaseCategory>,

    // holds all the prefix the last being the current suffix
    // s in L* algorithm
    prefix: Rc<BaseCategory::Object>,

    // holds the product of prefix and alphabet
    // FS in the L* algorithm
    prefix_alphabet: Rc<BaseCategory::Object>,

    hypothesis_prefix_alphabet: Rc<BaseCategory::Object>,

    // holds the suffixes of the last prefix
    // e in the L* algorithm
    suffix: Rc<BaseCategory::Object>,

    // holds the alphabet object
    // a in the L* algorithm
    alphabets: Rc<BaseCategory::Object>,

    // holds the observations
    // 2^E in the L* algorithm
    suffix_power_set: Rc<BaseCategory::Object>,

    oracle: Oracle,
}


impl <Oracle, BaseCategory> CALF<Oracle, BaseCategory>
where
    Oracle: OracleTrait<String>,
    BaseCategory: CategoryTrait<Morphism = Arrow<<BaseCategory as CategoryTrait>::Object, <BaseCategory as CategoryTrait>::Object>> + Hash + Eq + Clone + for<'a> From<Vec<&'a str>> + From<String>,
    <BaseCategory as CategoryTrait>::Object: Clone + From<String>,
    <<BaseCategory::Object as CategoryTrait>::Object as CategoryTrait>::Object: Clone + From<String>,
    <<BaseCategory as CategoryTrait>::Object as CategoryTrait>::Object: Clone + From<String> +
        From<Rc<<<<BaseCategory as CategoryTrait>::Object as CategoryTrait>::Object as CategoryTrait>::Object>>,
    <<BaseCategory as CategoryTrait>::Object as CategoryTrait>::Object:
{
    pub fn new(alphabets: Rc<BaseCategory::Object>, oracle: Oracle) -> Self where <BaseCategory as CategoryTrait>::Object: for<'a> From<Vec<&'a str>> {
        let mut category = EpicMonicCategory::<BaseCategory>::new();
        // add alphabet object to the category
        category.add_object(alphabets.clone()).expect("Failed to add alphabet object");

        // add prefix and suffix with empty.
        let prefix: Rc<BaseCategory::Object> = Rc::new(vec![""].into());
        category.add_object(prefix.clone()).expect("Failed to add prefix");

        let suffix: Rc<BaseCategory::Object> = Rc::new(vec![""].into());
        category.add_object(suffix.clone()).expect("Failed to add suffix");

        let suffix_power_set: Rc<BaseCategory::Object> = Rc::new(vec![""].into());
        category.add_object(suffix_power_set.clone()).expect("Failed to add observations");


        let prefix_alphabet = Rc::new(BaseCategory::Object::new());

        let mut result = CALF {
            category,
            prefix,
            suffix,
            alphabets,
            oracle,
            suffix_power_set,
            prefix_alphabet,
            hypothesis_prefix_alphabet: Rc::new(BaseCategory::Object::new()),
        };
        result.create_suffix_power_set().unwrap();
        // order matters here since in prefix alphabet we need suffix power set to be initialized first
        result.create_prefix_alphabet().unwrap();
        result
    }

    pub fn is_closed(&mut self) -> Result<Closed<BaseCategory::Object>, CalfErrors>
    {
        /*
        checks if wrapper is closed if not it creates a new suffix

        is closed if morphism closeW: FS -> H such that triangle commutes with estimation of f.

        FS ----F𝛼 ----> FQt --- δ --------> P
        |                                   |
        | closeW                            |β
        |                                   |
        |                                   |
        H ---------------m-----------------> 2^E

         */
        // start by checking if there is a morphism from FS to 2^e
        // there should be only one morphism from FS to 2^E
        let powerset_morphisms =
            self.get_or_create_morphism_to_powerset()?;
        let prefix_to_powerset = powerset_morphisms.0.clone();
        let prefix_alphabet_to_power_set = powerset_morphisms.1.clone();


        // Since this is a factorisation system there should be a morphism from S to H and H to 2^e
        // where its epic and monic respectively.
        // now we need to check if there exist a morphism from FS to H.

        // get epic and monic morphisms from prefix to powerset
        let morphism_factors = self.category.morphism_factors(&*prefix_to_powerset)?;
        let epic_morphism = morphism_factors.0.clone();
        let monic_morphism = morphism_factors.1.clone();

        // now we need to check if there is a morphism from FS to H
        let prefix_alphabet_to_h_homset = self.category.get_hom_set(&*self.prefix_alphabet,
                                                      &**epic_morphism.target_object())?;

        // there should be not more than one morphism from FS to H
        if prefix_alphabet_to_h_homset.len() > 1 {
            return Err(CalfErrors::MultipleMorphismsFromFSToH);
        }

        let prefix_alphabet_to_h = if prefix_alphabet_to_h_homset.is_empty() {
            // if there is no morphism, then we need to create one
            // create a new morphism from FS to H

            // since from H to powerset is monic
            // our mapping will map each obect in FS to object in H such that H maps to powerset
            let mut prefix_alphabet_to_h_mapping = HashMap::new();

            let monic_powerset_reverse_mapping: HashMap<_,_> = monic_morphism.arrow_mappings().iter()
                .map(|(source, target)| (target.clone(), source.clone())).collect();
            for (source_morphism, target_morphism) in prefix_alphabet_to_power_set.arrow_mappings() {
                // map each source morphism to a morphism in H
                // get morphism in monic morphism that maps to the target morphism
                if let Some(h_source_morphism) = monic_powerset_reverse_mapping.get(target_morphism) {
                    prefix_alphabet_to_h_mapping.insert(source_morphism.clone(), h_source_morphism.clone());
                }
                else{
                    // if there is no matching morphism in H, then its not closed
                    return Ok(Closed::NotClosed(HashSet::from_iter([source_morphism.clone()])));
                }

            }

            let morphism = Morphism::new(
                Uuid::new_v4().to_string(),
                self.prefix_alphabet.clone(),
                epic_morphism.target_object().clone(),
                prefix_alphabet_to_h_mapping
            );
            let morphisms  = self.category.add_morphism(Rc::new(morphism))?;
            morphisms.clone()
        } else {
            (*prefix_alphabet_to_h_homset.iter().last().unwrap().clone()).clone()
        };
        // if there is morphism we need to check if it commutes i.e
        // FS -> H -> powerset and FS -> power_set
        let commutation_result = self.category.morphism_commute(
            vec![&prefix_alphabet_to_h, &prefix_to_powerset],
            vec![&epic_morphism, &monic_morphism])?;

        match commutation_result {
            MorphismCommutationResult::Commutative => {
                // if it commutes, then we have a closed wrapper
                return Ok(Closed::Closed);
            },
            MorphismCommutationResult::NonCommutative(non_commuting_morphisms) => {
                // if it does not commute, then we have a not closed wrapper
                return Ok(Closed::NotClosed(non_commuting_morphisms));
            },
        }
    }


    fn get_or_create_prefix_to_powerset_morphism(&mut self) -> Result<&Rc<Morphism<CategorySubObjectAlias<BaseCategory>>>, CalfErrors>
    {
        let prefix_to_power_set = self.category.get_hom_set(&*self.prefix, &*self.suffix_power_set)?;

        // if there is more than one morphism, then there is an error somewhere since there should be only one morphism
        if prefix_to_power_set.len() > 1 {
            return Err(CalfErrors::MultipleMorphismsFromSuffixToPowerSet);
        }

        if prefix_to_power_set.is_empty() {
            // now we create a mapping from suffix to power set via membership query
            self.add_power_set_morphism(&self.prefix.clone())?;
            return self.get_or_create_prefix_to_powerset_morphism();
        }

        // here we have exactly one morphism from fs to power set and one from suffix to power set
        let prefix_to_power_set_morphism = self.category.get_hom_set(&*self.prefix, &*self.suffix_power_set)?;
        if prefix_to_power_set_morphism.is_empty() || prefix_to_power_set_morphism.len() > 1 {
            return Err(CalfErrors::UnknownError);
        }

        Ok(prefix_to_power_set_morphism.iter().last().unwrap())
    }

    fn get_or_create_prefix_alphabet_to_powerset_morphism(&mut self) -> Result<&Rc<Morphism<CategorySubObjectAlias<BaseCategory>>>, CalfErrors>
    {
        let prefix_alphabet_to_power_set =
            self.category.get_hom_set(&*self.prefix_alphabet, &*self.suffix_power_set)?;

        // there is more than one morphism, then there is an error somewhere since there should be only one morphism
        if prefix_alphabet_to_power_set.len() > 1 {
            return Err(CalfErrors::MultipleMorphismsFromFSToPowerSet);
        }

        if prefix_alphabet_to_power_set.is_empty() {
            // now we create a mapping from fs to power set via membership query
            self.add_power_set_morphism(&self.prefix_alphabet.clone())?;
            return self.get_or_create_prefix_alphabet_to_powerset_morphism();
        }

        // here we have exactly one morphism from fs to power set and one from suffix to power set
        let prefix_alphabet_to_power_set = self.category.get_hom_set(&*self.prefix_alphabet, &*self.suffix_power_set)?;
        if prefix_alphabet_to_power_set.is_empty() || prefix_alphabet_to_power_set.len() > 1 {
            return Err(CalfErrors::UnknownError);
        }

        Ok(prefix_alphabet_to_power_set.iter().last().unwrap())
    }

    fn get_or_create_morphism_to_powerset(&mut self) -> Result<(
        Rc<Morphism<CategorySubObjectAlias<BaseCategory>>>,
        Rc<Morphism<CategorySubObjectAlias<BaseCategory>>>), CalfErrors> where <<BaseCategory as CategoryTrait>::Object as CategoryTrait>::Object: From<String>
    {

       let prefix_to_power_set_morphism = self.get_or_create_prefix_to_powerset_morphism()?.clone();
       let prefix_alphabet_to_power_set = self.get_or_create_prefix_alphabet_to_powerset_morphism()?.clone();

        Ok((prefix_to_power_set_morphism, prefix_alphabet_to_power_set))
    }


    pub fn add_power_set_morphism(&mut self, object: &Rc<BaseCategory::Object>) -> Result<(), CalfErrors>
    {
        let mut mappings = HashMap::new();

        let suffix_objects = self.suffix.get_all_objects()?;
        // map identity morphism first.
        for sub_object in object.get_all_objects()? {
            let mut oracle_object = "".to_string();
            for suffix in &suffix_objects{
                let query = sub_object.category_id().to_owned() + suffix.category_id().clone();
                let query_result = self.oracle.membership_query(&query.to_string());
                oracle_object += &query_result.to_string();
            }
            // now find target object oracle object.
            println!("Mapping object {} to {}", sub_object.category_id(), oracle_object);
            println!("Suffix object");
            for s in self.suffix_power_set.get_all_objects()?{
                println!(" - {}", s.category_id());
            }
            let target_object = self.suffix_power_set.get_object(&<String as Into<<BaseCategory::Object as CategoryTrait>::Object>>::into(oracle_object))?;
            let target_identity_morphism = self.suffix_power_set.get_identity_morphism(&**target_object)?;
            mappings.insert(
                object.get_identity_morphism(&**sub_object)?.clone(),
                target_identity_morphism.clone()
            );
        }

        // create a new morphism from object to power set
        let morphism = Morphism::new(
            Uuid::new_v4().to_string(),
            object.clone(),
            self.suffix_power_set.clone(),
            mappings,
        );
        self.category.add_morphism(Rc::new(morphism))?;
        Ok(())
    }


    pub fn is_consistent(&self) -> Result<Consistent<BaseCategory::Object>, CalfErrors> {
        /*
        checks if the wrapper is consistent with the oracle
        i.e. for every (s,a) ∈ FS, there exists s′ ∈ S such that:
        FS(s,a) ∈ FS, there exists s′ ∈ S such that:

            (β∘δ∘Fα)(s,a)=(β∘α)(s′)

        then you can define:
            close W(s,a) = ew(s′) ∈ Hw
         */

        Ok(Consistent::Consistent)
    }

    pub fn run(&mut self) -> Result<(), CalfErrors>
    {
        loop {

            match self.is_closed()? {
                Closed::Closed => {
                    // if closed, then we can check if it is consistent
                    if matches!(self.is_consistent()?, Consistent::Consistent) {
                        // if consistent, then we can stop
                        break;
                    }
                },
                Closed::NotClosed(non_closed_morphisms) => {
                    // if not closed, then we add a new prefix
                    let mut new_prefix = (*self.prefix).clone();
                    for obj in non_closed_morphisms {
                        // for each non closed morphism, we need to add a new prefix
                        // i.e. we need to add a new object to the suffix
                        let new_object = obj.source_object().clone();
                        new_prefix.add_object(new_object)?;
                    }
                    let new_prefix = Rc::new(new_prefix);
                    self.category.add_object(new_prefix.clone())?;
                    self.prefix = new_prefix;
                    self.create_prefix_alphabet();
                    continue;
                },
            }

            match self.is_consistent()? {
                Consistent::NotConsistent(non_consistent_morphisms) => {
                    // if not consistent, then we need to add a new suffix
                    let mut new_suffix = (*self.suffix).clone();
                    for morphism in non_consistent_morphisms {
                        // for each non consistent morphism, we need to add a new object to the suffix
                        let new_object = morphism.source_object().clone();
                        new_suffix.add_object(new_object)?;
                    }
                    let new_suffix = Rc::new(new_suffix);
                    self.category.add_object(new_suffix.clone())?;
                    self.suffix = new_suffix;
                    self.create_suffix_power_set()?;
                },
                Consistent::Consistent => {
                    // if consistent and closed, then we can stop
                    if matches!(self.is_closed()?, Closed::Closed){
                        break;
                    }
                },

            }
        }
        Ok(())
    }

    pub fn make_closed(&mut self) -> Result<(), CalfErrors> {
        /*
        checks if wrapper is closed if not it creates a new suffix

        is closed if morphism closeW: FS -> H such that triangle commutes with estimation of f.

        FS ----F𝛼 ----> FQt --- δ --------> P
        |                                   |
        | closeW                            |β
        |                                   |
        |                                   |
        H ---------------m-----------------> 2^E


        for t in s.a there exist s such that row(s) == row(s.a)

        The wrapper (α,β) is closed if there exists a morphism:

            close W:FS ----> Hw

            such that

                (β∘δ∘Fα)=mW∘close W


        (β∘δ∘Fα)(s,a)(e)=L(sae)

        If for every (s,a) ∈ FS, there exists s′ ∈ S such that:
        FS(s,a) ∈ FS, there exists s′ ∈ S such that:

            (β∘δ∘Fα)(s,a)=(β∘α)(s′)

        then you can define:
            close W(s,a) = ew(s′) ∈ Hw

         */

        // create observation table
        // add morphism from suffix to observations

        Ok(())
    }

    pub fn make_consistent(&mut self) -> Result<(), CalfErrors> {
        todo!()
    }

    fn create_prefix_alphabet(&mut self) -> Result<(), CalfErrors> {
        let powerset_morphism = self.get_or_create_prefix_to_powerset_morphism()?.clone();
        let morphism_factors =
            self.category.morphism_factors(&*powerset_morphism)?;
        let epic_morphism = morphism_factors.0.clone();

        let product_mappings = apply_product(
            &mut self.category,
            &self.prefix,
            self.alphabets.clone()).expect("Failed to apply");

        let prefix_identity_morphism = self.category.get_identity_morphism(&*self.prefix)?;
        if let Some(prefix_alphabet_identity_morphism) = product_mappings.get(prefix_identity_morphism) {
            self.prefix_alphabet = prefix_alphabet_identity_morphism.source_object().clone();
        } else {
            return Err(CalfErrors::UnknownError);
        }

        // now create hypothesis prefix alphabet
        if let Some(hypothesis_prefix_alphabet_identity_morphism) = product_mappings.get(&epic_morphism) {
            self.hypothesis_prefix_alphabet = hypothesis_prefix_alphabet_identity_morphism.source_object().clone();
        } else {
            return Err(CalfErrors::UnknownError);
        }

        Ok(())
    }

    fn create_suffix_power_set(&mut self) -> Result<(), CalfErrors> {
        // create all possible 2^E
        let mut power_set = BaseCategory::Object::new();
        let n = self.suffix.get_all_objects()?.len();

        for i in 0..(1 << n) {
            // add each element to the power set
            let mut row = "".to_string();
            for j in 0..n {
                let value: bool = (i & (1 << j)) != 0;
                row += &value.to_string();
            }

            power_set.add_object(Rc::new(<BaseCategory::Object as CategoryTrait>::Object::from(row)))?;
        }
        let power_set = Rc::new(power_set);
        // add the power set to the category
        self.category.add_object(power_set.clone())?;
        self.suffix_power_set = power_set;
        Ok(())
    }
}


