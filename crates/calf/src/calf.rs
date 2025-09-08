use std::hash::Hash;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use uuid::Uuid;
use category_theory::core::traits::category_trait::{CategorySubObjectAlias, CategoryTrait, MorphismCommutationResult};
use category_theory::core::functor::Functor;
use category_theory::core::morphism::Morphism;
use category_theory::core::product_endofunctor::apply_product;
use category_theory::core::traits::arrow_trait::ArrowTrait;
use category_theory::core::epic_monic_category::EpicMonicCategory;
use category_theory::core::expand_functor::expand_functor;
use category_theory::core::traits::factorization_system_trait::FactorizationSystemTrait;
use category_theory::core::traits::functor_trait::FunctorTrait;
use category_theory::core::traits::morphism_trait::MorphismTrait;
use category_theory::core::unit::unit_category::UnitCategory;
use crate::calf_errors::CalfErrors;
use crate::oracle_trait::{OracleTrait, QueryInputTrait};


enum Closed<Category: CategoryTrait> {
    Closed,
    NotClosed(HashSet<Morphism<Category::Object>>),
}


enum Consistent<Category: CategoryTrait> {
    Consistent,
    NotConsistent(HashSet<Morphism<Category::Object>>),
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

    prefix_alphabet: Rc<BaseCategory::Object>,

    flatten_prefix_alphabet: Rc<BaseCategory::Object>,

    // holds the suffixes of the last prefix
    // e in the L* algorithm
    suffix: Rc<BaseCategory::Object>,

    alphabets: Rc<BaseCategory::Object>,

    suffix_power_set: Rc<BaseCategory::Object>,

    oracle: Oracle,
}


impl <
    Oracle: OracleTrait<String>,
    BaseCategory: CategoryTrait + Hash + Eq + Clone + for<'a> From<Vec<&'a str>> + From<String>
> CALF<Oracle, BaseCategory>
where
    <BaseCategory as CategoryTrait>::Object: Clone + From<String>,
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
            flatten_prefix_alphabet: Rc::new(BaseCategory::Object::new()),
        };
        result.create_prefix_alphabet().unwrap();
        result.create_suffix_power_set();

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
        let flattened_prefix_alphabet_to_power_set = powerset_morphisms.1.clone();


        // Since this is a factorisation system there should be a morphism from S to H and H to 2^e
        // where its epic and monic respectively.
        // now we need to check if there exist a morphism from FS to H.

        // get epic and monic morphisms from prefix to powerset
        let morphism_factors = self.category.morphism_factors(&*prefix_to_powerset)?;
        let epic_morphism = morphism_factors.0.clone();
        let monic_morphism = morphism_factors.1.clone();

        // now we need to check if there is a morphism from FS to H
        let flatten_prefix_alphabet_to_h_homset = self.category.get_hom_set(&*self.flatten_prefix_alphabet,
                                                      &**epic_morphism.target_object())?;

        // there should be not more than one morphism from FS to H
        if flatten_prefix_alphabet_to_h_homset.len() > 1 {
            return Err(CalfErrors::MultipleMorphismsFromFSToH);
        }

        let flatten_prefix_alphabet_to_h = if flatten_prefix_alphabet_to_h_homset.is_empty() {
            // if there is no morphism, then we need to create one
            // create a new morphism from FS to H

            // since from H to powerset is monic
            // our mapping will map each obect in FS to object in H such that H maps to powerset
            let mut flatten_prefix_alphabet_to_h_mapping = HashMap::new();

            let monic_powerset_reverse_mapping: HashMap<_,_> = monic_morphism.functor()?.arrow_mappings().iter()
                .map(|(source, target)| (target.clone(), source.clone())).collect();
            for (source_morphism, target_morphism) in flattened_prefix_alphabet_to_power_set.functor()?.arrow_mappings() {
                // map each source morphism to a morphism in H
                // get morphism in monic morphism that maps to the target morphism
                if let Some(h_source_morphism) = monic_powerset_reverse_mapping.get(target_morphism) {
                    flatten_prefix_alphabet_to_h_mapping.insert(source_morphism.clone(), h_source_morphism.clone());
                }
                else{
                    // if there is no matching morphism in H, then its not closed
                    return Ok(Closed::NotClosed(HashSet::from_iter([(**source_morphism).clone()])));
                }

            }

            let morphism = Morphism::new(
                Uuid::new_v4().to_string(),
                self.prefix_alphabet.clone(),
                epic_morphism.target_object().clone(),
                Rc::new(Functor::new(
                    Uuid::new_v4().to_string(),
                    self.prefix_alphabet.clone(),
                    epic_morphism.target_object().clone(),
                    flatten_prefix_alphabet_to_h_mapping,
                )),
            );
            let morphisms  = self.category.add_morphism(Rc::new(morphism))?;
            morphisms.clone()
        } else {
            (*flatten_prefix_alphabet_to_h_homset.iter().last().unwrap().clone()).clone()
        };
        // if there is morphism we need to check if it commutes i.e
        // FS -> H -> powerset and FS -> power_set
        let commutation_result = self.category.morphism_commute(
            vec![&flatten_prefix_alphabet_to_h, &prefix_to_powerset],
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

    fn get_or_create_morphism_to_powerset(&mut self) -> Result<(
        &Rc<Morphism<CategorySubObjectAlias<BaseCategory>>>,
        &Rc<Morphism<CategorySubObjectAlias<BaseCategory>>>), CalfErrors> where <<BaseCategory as CategoryTrait>::Object as CategoryTrait>::Object: From<String>
    {

        let prefix_to_power_set = self.category.get_hom_set(&*self.prefix, &*self.suffix_power_set)?;

        // if there is more than one morphism, then there is an error somewhere since there should be only one morphism
        if prefix_to_power_set.len() > 1 {
            return Err(CalfErrors::MultipleMorphismsFromSuffixToPowerSet);
        }

        let flatten_prefix_alphabet_to_power_set =
            self.category.get_hom_set(&*self.flatten_prefix_alphabet, &*self.suffix_power_set)?;

        // there is more than one morphism, then there is an error somewhere since there should be only one morphism
        if flatten_prefix_alphabet_to_power_set.len() > 1 {
            return Err(CalfErrors::MultipleMorphismsFromFSToPowerSet);
        }


        if prefix_to_power_set.is_empty() {
            // now we create a mapping from suffix to power set via membership query
            self.add_power_set_morphism(&self.prefix.clone())?;
            return self.get_or_create_morphism_to_powerset();
        }

        // now if there is no morphism, then we need to create one
        if flatten_prefix_alphabet_to_power_set.is_empty() {
            // now we create a mapping from fs to power set via membership query
            self.add_power_set_morphism(&self.flatten_prefix_alphabet.clone())?;
            return self.get_or_create_morphism_to_powerset();
        }

        // here we have exactly one morphism from fs to power set and one from suffix to power set
        let flatten_prefix_alphabet_to_power_set = self.category.get_hom_set(&*self.flatten_prefix_alphabet, &*self.suffix_power_set)?;
        if flatten_prefix_alphabet_to_power_set.is_empty() || flatten_prefix_alphabet_to_power_set.len() > 1 {
            return Err(CalfErrors::UnknownError);
        }


        let prefix_to_power_set_morphism = self.category.get_hom_set(&*self.prefix, &*self.suffix_power_set)?;
        if prefix_to_power_set_morphism.is_empty() || prefix_to_power_set_morphism.len() > 1 {
            return Err(CalfErrors::UnknownError);
        }

        Ok((prefix_to_power_set_morphism.iter().last().unwrap(), flatten_prefix_alphabet_to_power_set.iter().last().unwrap()))
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
            Rc::new(Functor::new(
                Uuid::new_v4().to_string(),
                object.clone(),
                self.suffix_power_set.clone(),
                mappings,
            )),
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
        let prefix_alphabet_functor = apply_product(self.prefix.clone(),
                               self.alphabets.clone()).expect("Failed to apply");

        // add the object to the category
        self.category.add_object(prefix_alphabet_functor.target_object().clone())
            .expect("Failed to add product object to the category");
        self.prefix_alphabet = prefix_alphabet_functor.target_object().clone();

        // add morphism from prefix to prefix alphabet
        let prefix_to_prefix_alphabet_morphism = Morphism::new(
            Uuid::new_v4().to_string(),
            self.prefix.clone(),
            self.prefix_alphabet.clone(),
            prefix_alphabet_functor.clone(),
        );
        self.category.add_morphism(Rc::new(prefix_to_prefix_alphabet_morphism))
            .expect("Failed to add prefix to prefix alphabet morphism");

        // now create a flattened version of the prefix
        let flattened_prefix_alphabet_functor =
            expand_functor(prefix_alphabet_functor.target_object())?;

        // add the flattened prefix alphabet to the category
        for (index, functor) in flattened_prefix_alphabet_functor.iter().enumerate() {
            if index == 0 {
                self.category.add_object(functor.target_object().clone())?;
                self.flatten_prefix_alphabet = functor.target_object().clone();
            }
            // add morphism from prefix alphabet to flattened prefix alphabet
            let morphism = Morphism::new(
                Uuid::new_v4().to_string(),
                self.prefix_alphabet.clone(),
                functor.target_object().clone(),
                functor.clone().into(),
            );
            self.category.add_morphism(Rc::new(morphism));
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

// impl CALF {
//     pub fn new(alphabets: Vec<String>) -> Self {
//         let mut category = SetCategory::new();
//
//         let alphabet_object = CategoryObject{
//             id: Uuid::new_v4(),
//             value: SetCategoryObj::vec_to_bases(alphabets),
//         };
//         category.add_object(alphabet_object);
//
//         // add initial object
//         let initial_object = CategoryObject{
//             id: Uuid::new_v4(),
//             value: SetCategoryObj::vec_to_bases(vec![]),
//         };
//         category.add_object(initial_object);
//
//         // add terminal object
//         let terminal_object = CategoryObject{
//             id: Uuid::new_v4(),
//             value: SetCategoryObj::vec_to_bases(vec![()])
//         };
//         category.add_object(terminal_object);
//
//         // adding Qt object
//         let qt_object = CategoryObject{
//             id: Uuid::new_v4(),
//             value: SetCategoryObj::vec_to_bases(vec!["Qt".to_string()]),
//         };
//         category.add_object(qt_object);
//
//
//         // wrapper morphisms alpha and beta
//         let morphims_alpha = Morphism::new(UuidMorphismId::new(),
//         initial_object, qt_object, false);
//         inner.add_morphism(morphims_alpha.clone());
//
//         let morphims_beta = Morphism::new(UuidMorphismId::new(),
//          qt_object, terminal_object, false);
//         inner.add_morphism(morphims_beta.clone());
//
//         CALF {
//             category,
//             wrapper: (morphims_alpha, morphims_beta),
//             alphabets_object_id: alphabet_object.id.clone(),
//             product_endofunctor: ProductEndoFunctor::new(&category, &alphabet_object.id),
//         }
//     }
//
//     pub fn is_close(&self) -> bool {
//         /*
//         is closed if morphism closeW: FS -> H such that triangle commutes with estimation of f.
//
//         FS ----F𝛼 ----> FQt --- δ --------> P
//         |                                   |
//         | closeW                            |β
//         |                                   |
//         |                                   |
//         H ---------------m-----------------> 2^E
//
//
//         for t in s.a there exist s such that row(s) == row(s.a)
//
//         The wrapper (α,β) is closed if there exists a morphism:
//
//             close W:FS ----> Hw
//
//             such that
//
//                 (β∘δ∘Fα)=mW∘close W
//
//
//         (β∘δ∘Fα)(s,a)(e)=L(sae)
//
//         If for every (s,a) ∈ FS, there exists s′ ∈ S such that:
//         FS(s,a) ∈ FS, there exists s′ ∈ S such that:
//
//             (β∘δ∘Fα)(s,a)=(β∘α)(s′)
//
//         then you can define:
//             close W(s,a) = ew(s′) ∈ Hw
//
//          */
//
//         // apply endo functor to S
//         let fs = self.product_endofunctor
//             .fmap_object(self.wrapper.0.source_id.clone());
//
//         // we have mw: H -> P (monic morphsim) provided by factorisation system
//         let mw = self.wrapper.1.clone();
//         // apply mw morphism
//         let h_to_p = mw.apply();
//
//         // for wrapper to be closed, there should exist a morphism closeW: FS -> Hw
//         // such that the triangle commutes
//         // i.e. (β∘δ∘Fα) = mw∘close W
//         // (β∘δ∘Fα) is equivalent to membership query.
//         // apply FS to membership query.
//
//         let candidate_close_w_morphism = Morphism::new(
//             UuidMorphismId::new(),
//             fs.id.clone(),
//             mw.target_id.clone(),
//             false,
//         );
//
//
//         // since mw is monic, for morhism to exist that is commutative, for every (s,a) ∈ FS to P,
//         // there should exist simmilar output from H to P
//         for (s, a) in fs.iter() {
//             // FS to P is given by morphism (β∘δ∘Fα) which is the membership query
//             for e in self.category.get_object(self.suffix_id).unwrap().value.iter(){
//                 let fs_to_p = self.oracle.membership_query(s + a + e);
//
//                 // check if fs_to_p exist in h_to_p
//                 if h_to_p.contains(&fs_to_p){
//                     // add the map of s.a to the translating hw
//                 }
//                 else{
//                     // meaning it's not closed and we need to update the wrapper to new S such that
//                     // the missing s.a is added
//                 }
//             }
//         }
//
//
//         false
//     }
//
//
//
// }

