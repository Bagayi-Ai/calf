use std::hash::Hash;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use uuid::Uuid;
use category_theory::core::traits::category_trait::{CategorySubObjectAlias, CategoryTrait, MorphismCommutationResult, CategoryFromObjects, CategoryCloneWithNewId};
use category_theory::core::arrow::{Morphism, Arrow};
use category_theory::core::cytosjsexport::save_category_to_cytoscape_json_file;
use category_theory::core::functor::Functor;
use category_theory::core::product_endofunctor::apply_product;
use category_theory::core::traits::arrow_trait::ArrowTrait;
use category_theory::core::epic_monic_category::EpicMonicCategory;
use category_theory::core::object_id::ObjectId;
use category_theory::core::traits::factorization_system_trait::FactorizationSystemTrait;
use crate::calf_errors::CalfErrors;
use category_theory::core::functors::inclusion_functor::inclusion_functor;
use crate::oracle_trait::{OracleTrait, QueryInputTrait};
use category_theory::core::identifier::Identifier;
use category_theory::core::persistable_category::PersistableCategory;
use category_theory::core::persistable_factorization_category::PersistableFactorizationCategory;

enum Closed<Category: CategoryTrait> {
    Closed,
    NotClosed(HashSet<Arc<Category::Morphism>>),
}


enum Consistent<Category: CategoryTrait> {
    Consistent,
    NotConsistent(HashSet<Arc<Category::Morphism>>),
}


pub struct CALF<
    Oracle: OracleTrait<String>,
    BaseCategory: CategoryTrait<
        Morphism = Arrow<<BaseCategory as CategoryTrait>::Object,
            <BaseCategory as CategoryTrait>::Object>> + Hash + Eq + Clone
>
where
    <BaseCategory as CategoryTrait>::Object: Clone + From<String> + CategoryCloneWithNewId,
    <<BaseCategory as CategoryTrait>::Object as CategoryTrait>::Object: Clone,
{
    category: PersistableFactorizationCategory<EpicMonicCategory<BaseCategory>>,

    // holds all the prefix the last being the current suffix
    // s in L* algorithm
    prefix: Arc<BaseCategory::Object>,

    // holds the product of prefix and alphabet
    // FS in the L* algorithm
    prefix_alphabet: Arc<BaseCategory::Object>,

    hypothesis_prefix_alphabet: Arc<BaseCategory::Object>,

    // holds the suffixes of the last prefix
    // e in the L* algorithm
    suffix: Arc<BaseCategory::Object>,

    // holds the alphabet object
    // a in the L* algorithm
    alphabets: Arc<BaseCategory::Object>,

    // holds the observations
    // 2^E in the L* algorithm
    suffix_power_set: Arc<BaseCategory::Object>,

    oracle: Oracle,
}


impl <Oracle, BaseCategory> CALF<Oracle, BaseCategory>
where
    Oracle: OracleTrait<String>,
    BaseCategory: CategoryTrait<Morphism = Arrow<<BaseCategory as CategoryTrait>::Object, <BaseCategory as CategoryTrait>::Object>> + Hash + Eq + Clone ,
    BaseCategory::Object: Clone + From<String> + CategoryCloneWithNewId,
    <BaseCategory::Object as CategoryTrait>::Object : Clone + From<String> + for<'a> From<&'a str>,
    <<BaseCategory::Object as CategoryTrait>::Object as CategoryTrait>::Object: Clone + From<String> + From<ObjectId>,
{
    pub async fn new(alphabets: Arc<BaseCategory::Object>, oracle: Oracle) -> Self
    {
        let mut category =
            PersistableFactorizationCategory::new().await.unwrap();
        // add alphabet object to the category
        category.add_object(alphabets.clone()).await.expect("Failed to add alphabet object");

        // add prefix and suffix with empty.
        let prefix: Arc<BaseCategory::Object> = Arc::new(BaseCategory::Object::from_objects(vec![""]).await.unwrap());
        category.add_object(prefix.clone()).await.expect("Failed to add prefix");

        let suffix: Arc<BaseCategory::Object> = Arc::new(BaseCategory::Object::from_objects(vec![""]).await.unwrap());
        category.add_object(suffix.clone()).await.expect("Failed to add suffix");

        let suffix_power_set: Arc<BaseCategory::Object> =Arc::new(BaseCategory::Object::from_objects(vec![""]).await.unwrap());
        category.add_object(suffix_power_set.clone()).await.expect("Failed to add observations");


        let prefix_alphabet = Arc::new(BaseCategory::Object::new().await.unwrap());

        let mut result = CALF {
            category,
            prefix,
            suffix,
            alphabets,
            oracle,
            suffix_power_set,
            prefix_alphabet,
            hypothesis_prefix_alphabet: Arc::new(BaseCategory::Object::new().await.unwrap()),
        };
        result.create_suffix_power_set().await.unwrap();
        // order matters here since in prefix alphabet we need suffix power set to be initialized first
        result.create_prefix_alphabet().await.unwrap();
        result
    }

    pub async fn run(&mut self) -> Result<(), CalfErrors>
    {
        loop {

            match self.is_closed().await? {
                Closed::Closed => {
                    // if closed, then we can check if it is consistent
                    if matches!(self.is_consistent().await?, Consistent::Consistent) {
                        // if consistent, then we can stop
                        break;
                    }
                },
                Closed::NotClosed(non_closed_morphisms) => {
                    // if not closed, then we need to add a new prefix
                    let new_prefix = self.update_table(
                        &self.prefix.clone(), non_closed_morphisms).await?;
                    self.prefix = new_prefix;
                    self.create_prefix_alphabet().await?;
                    continue;
                },
            }

            match self.is_consistent().await? {
                Consistent::NotConsistent(non_consistent_morphisms) => {
                    // if not consistent, then we need to add a new suffix
                    let new_suffix = self.update_table(
                        &self.suffix.clone(), non_consistent_morphisms).await?;
                    self.suffix = new_suffix;
                    self.create_suffix_power_set().await?;
                },
                Consistent::Consistent => {
                    // if consistent and closed, then we can stop
                    if matches!(self.is_closed().await?, Closed::Closed){
                        break;
                    }
                },

            }
        }
        let final_hypothesis_transition = self.get_or_add_hypothesis_transition().await?;

        // print states
        let states = final_hypothesis_transition.target_object();
        println!("States: {:?}", states.get_all_objects().await?);

        // print transitions
        let transitions = final_hypothesis_transition.arrow_mappings();
        println!("Transitions: {:?}", transitions);
        Ok(())
    }

    pub async fn is_closed(&mut self) -> Result<Closed<BaseCategory::Object>, CalfErrors>
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
            self.get_or_create_morphism_to_powerset().await?;
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
                                                      &**epic_morphism.target_object()).await?;

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

            let monic_powerset_reverse_mapping: HashMap<_,_> = monic_morphism.arrow_mappings().into_iter().flatten()
                .map(|(source, target)| (target.clone(), source.clone())).collect();
            for (source_morphism, target_morphism) in prefix_alphabet_to_power_set.arrow_mappings().into_iter().flatten() {
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

            let morphism = Arc::new(Morphism::new_with_mappings(
                self.prefix_alphabet.clone(),
                epic_morphism.target_object().clone(),
                prefix_alphabet_to_h_mapping
            ));
            self.category.add_morphism(morphism.clone()).await?;
            morphism.clone()
        } else {
            (*prefix_alphabet_to_h_homset.iter().last().unwrap().clone()).clone()
        };
        // if there is morphism we need to check if it commutes i.e
        // FS -> H -> powerset and FS -> power_set
        let commutation_result = self.category.morphism_commute(
            vec![&prefix_alphabet_to_h, &prefix_to_powerset],
            vec![&epic_morphism, &monic_morphism]).await?;

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

    pub async fn is_consistent(&mut self) -> Result<Consistent<BaseCategory::Object>, CalfErrors> {
        /*
        checks if the wrapper is consistent with the oracle
        i.e. for every (s,a) ∈ FS, there exists s′ ∈ S such that:
        FS(s,a) ∈ FS, there exists s′ ∈ S such that:

            (β∘δ∘Fα)(s,a)=(β∘α)(s′)

        then you can define:
            close W(s,a) = ew(s′) ∈ Hw


            FS ----F𝛼 ----> FQt --- δ --------> P
            |                                   |
            | Fe                                |β
            |                                   |
            |                                   |
            FH ---------consistent f------------> 2^E
         */
        // get morphism from FS to 2^E
        let powerset_morphisms =
            self.get_or_create_morphism_to_powerset().await?;
        let prefix_alphabet_to_power_set = powerset_morphisms.1.clone();

        // prefix alphabet to hypothesis prefix alphabet
        let fs_to_fh_morphisms =
            self.category.get_hom_set(&*self.prefix_alphabet, &*self.hypothesis_prefix_alphabet).await?;
        if fs_to_fh_morphisms.len() > 1 {
            return Err(CalfErrors::MultipleMorphismsFromFStoFH);
        }
        if fs_to_fh_morphisms.is_empty() {
            return Err(CalfErrors::NoMorphismFromFStoFH);
        }

        let fs_to_fh =
            fs_to_fh_morphisms.into_iter().last().unwrap().clone();

        // now we need to check if there is a morphism from FH to 2^E
        let fh_to_powerset_morphisms =
            self.category.get_hom_set(&*self.hypothesis_prefix_alphabet, &*self.suffix_power_set).await?;

        if fh_to_powerset_morphisms.len() > 1 {
            return Err(CalfErrors::MultipleMorphismsFromFHtoPowerset);
        }

        let fh_to_powerset = if fh_to_powerset_morphisms.is_empty() {
            // if there is no morphism, then we need to create one
            // create a new morphism from FH to 2^E

            // since from FS to FH is epic
            // for it to commute our mapping will map each object in FH to object in powerset such that FS maps to powerset
            let mut fh_to_powerset_mapping = HashMap::new();

            let fs_to_powerset_mapping: HashMap<_,_> = prefix_alphabet_to_power_set.arrow_mappings().into_iter().flatten().collect();
                // .map(|(source, target)| (source.clone(), target.clone())).collect();
            let fs_to_fh_mapping: HashMap<_, _> = fs_to_fh.arrow_mappings().into_iter().flatten().collect();
            for (source_morphism, target_morphism) in fs_to_powerset_mapping {
                // get morphism in epic morphism that maps to the target morphism
                if let Some(fh_morphism) = fs_to_fh_mapping.get(&source_morphism)
                {
                    // check if this morphism is already mapped to the powerset
                    if let Some(existing_mapping) = fh_to_powerset_mapping.get(*fh_morphism) {
                        // if it is already mapped, then check if it maps to the same target
                        if existing_mapping != target_morphism {
                            return Ok(Consistent::NotConsistent(HashSet::from_iter([source_morphism.clone()])));
                        }
                        // if it maps to the same target, then continue
                        continue;
                    }
                    else{
                        // if it is not mapped, then map it
                        fh_to_powerset_mapping.insert(fh_morphism.clone().clone(), target_morphism.clone());
                    }
                }
                else{
                    return Err(CalfErrors::InvalidMappingFromFStoFH)
                }
            }

            let morphism = Arc::new(Morphism::new_with_mappings(
                self.hypothesis_prefix_alphabet.clone(),
                self.suffix_power_set.clone(),
                fh_to_powerset_mapping
            ));
            self.category.add_morphism(morphism.clone()).await?;
            morphism.clone()
        } else {
            (*fh_to_powerset_morphisms.iter().last().unwrap().clone()).clone()
        };

        // if there is morphism we need to check if it commutes i.e
        // FS -> FH -> powerset and FS -> power_set
        let commutation_result = self.category.morphism_commute(
            vec![&fs_to_fh, &fh_to_powerset],
            vec![&prefix_alphabet_to_power_set]).await?;
        // match commutation_result {
        //     MorphismCommutationResult::Commutative => {
        //         // if it commutes, then we have a consistent wrapper
        //         return Ok(Consistent::Consistent);
        //     },
        //     MorphismCommutationResult::NonCommutative(non_commuting_morphisms) => {
        //         // if it does not commute, then we have a not consistent wrapper
        //         return Ok(Consistent::NotConsistent(non_commuting_morphisms));
        //     },
        // }
        Ok(Consistent::Consistent)
    }


    pub async fn get_or_add_hypothesis_transition(&mut self) -> Result<Arc<BaseCategory::Morphism>, CalfErrors> {
        /*
        FS ---Fe(epic)---> FH
        |                 |
        | Closed          | Consistent
        |                 |
        H ----monic ----> 2^E

        hypothesis transition function is given by:
          morphism from FH to H that makes the two triangles commute.

         */
        let fs_to_fh_morphisms =
            self.category.get_hom_set(&*self.prefix_alphabet, &*self.hypothesis_prefix_alphabet).await?;
        if fs_to_fh_morphisms.len() != 1 {
            return Err(CalfErrors::MultipleMorphismsFromFStoFH);
        }
        let fs_to_fh =
            fs_to_fh_morphisms.into_iter().last().unwrap().clone();


        let fh_to_powerset_morphisms =
            self.category.get_hom_set(&*self.hypothesis_prefix_alphabet, &*self.suffix_power_set).await?;
        if fh_to_powerset_morphisms.len() != 1 {
            return Err(CalfErrors::MultipleMorphismsFromFHtoPowerset);
        }
        let fh_to_powerset = fh_to_powerset_morphisms.into_iter().last().unwrap().clone();

        // get epic and monic morphisms from prefix to powerset
        let powerset_morphism = self.get_or_create_prefix_to_powerset_morphism().await?.clone();
        let morphism_factors = self.category.morphism_factors(&*powerset_morphism)?;
        let monic_morphism = morphism_factors.1.clone();
        let monic_morphism_mapping = monic_morphism.arrow_mappings().into_iter().flatten().collect::<HashMap<_,_>>();
        let hypothesis = monic_morphism.source_object().clone();

        let fs_to_h = self.category.get_hom_set(&*self.prefix_alphabet, &*hypothesis).await?;
        if fs_to_h.len() != 1 {
            return Err(CalfErrors::MultipleMorphismsFromFStoH);
        }
        let fs_to_h = fs_to_h.into_iter().last().unwrap().clone();


        // now we need to find a morphism from FH to H that makes the two triangles commute.
        let mut fh_to_h_mappings = HashMap::new();
        let fs_to_h_mappings: HashMap<_, _> = fs_to_h.arrow_mappings().into_iter().flatten().collect();
        let fs_to_powerset_mappings: HashMap<_, _> = fh_to_powerset.arrow_mappings().into_iter().flatten().collect();

        for (fs_morphism, fh_morphism) in fs_to_fh.arrow_mappings().into_iter().flatten() {
            // get where its mapped in H
            if let Some(h_morphism) = fs_to_h_mappings.get(fs_morphism){
                // now add it to fh to h mapping if it is not already there
                if let Some(existing_mapping) = fh_to_h_mappings.get(fh_morphism) {
                    // if it is already mapped, then check if it maps to the same target
                    if existing_mapping != *h_morphism {
                        return Err(CalfErrors::InvalidMappingFromFStoFH);
                    }
                }
                else{
                    // if it is not mapped, then map it
                    fh_to_h_mappings.insert(fh_morphism.clone(), h_morphism.clone().clone());
                }

                // now check that it commutes with the other triangle
                // fh_morphism -> powerset should be the same as fs_morphism -> h -> powerset
                if let Some(fh_powerset_morphism) = fs_to_powerset_mappings.get(fh_morphism){
                    // should be the same as h -> powerset
                    if let Some(h_powerset_morphism) = monic_morphism_mapping.get(h_morphism){
                        if fh_powerset_morphism != h_powerset_morphism {
                            return Err(CalfErrors::InvalidMappingFromFHtoPowerset);
                        }
                    }
                    else{
                        return Err(CalfErrors::InvalidMappingFromHtoPowerset);
                    }
                }
                else{
                    return Err(CalfErrors::InvalidMappingFromFHtoPowerset);
                }
            }
            else {
                return Err(CalfErrors::InvalidMappingFromFStoFH);
            }
        }

        let new_morphism = Arc::new(BaseCategory::Morphism::new_with_mappings(
            self.hypothesis_prefix_alphabet.clone(),
            hypothesis.clone(),
            fh_to_h_mappings
        ));

        self.category.add_morphism(new_morphism.clone()).await?;
        Ok(new_morphism)
    }

    async fn create_prefix_alphabet(&mut self) -> Result<(), CalfErrors> {
        let prefix_to_powerset_morphism=
            self.get_or_create_prefix_to_powerset_morphism().await?.clone();
        let morphism_factors =
            self.category.morphism_factors(&*prefix_to_powerset_morphism)?;
        // epic morphism from S (prefix) to H (hypothesis)
        let epic_morphism = morphism_factors.0.clone();

        let (product_object, product_mapping) = apply_product(
            &mut self.category,
            &self.prefix,
            self.alphabets.clone()).await.expect("Failed to apply");

        self.prefix_alphabet = product_object;

        // now create hypothesis prefix alphabet
        if let Some(hypothesis_prefix_alphabet_identity_morphism) = product_mapping.get(&epic_morphism) {
            self.hypothesis_prefix_alphabet = hypothesis_prefix_alphabet_identity_morphism.target_object().clone();
        } else {
            return Err(CalfErrors::UnknownError);
        }

        Ok(())
    }

    async fn create_suffix_power_set(&mut self) -> Result<(), CalfErrors> {
        // create all possible 2^E
        let mut power_set = BaseCategory::Object::new().await?;
        let n = self.suffix.get_all_objects().await?.len();

        for i in 0..(1 << n) {
            // add each element to the power set
            let mut row = "".to_string();
            for j in 0..n {
                let value: bool = (i & (1 << j)) != 0;
                row += &value.to_string();
            }

            power_set.add_object(Arc::new(<BaseCategory::Object as CategoryTrait>::Object::from(row))).await?;
        }
        let power_set = Arc::new(power_set);
        // add the power set to the category
        self.category.add_object(power_set.clone()).await?;
        self.suffix_power_set = power_set;
        Ok(())
    }

    async fn get_or_create_prefix_to_powerset_morphism(&mut self) -> Result<Arc<Morphism<CategorySubObjectAlias<BaseCategory>>>, CalfErrors>
    {
        let mut already_added = false;
        loop {
            let prefix_to_power_set =
                self.category.get_hom_set(&*self.prefix.clone(), &*self.suffix_power_set).await?;
            // let prefix_to_power_set: Vec<_> = prefix_to_power_set.iter().map(|m| m.to_owned()).collect();

            // if there is more than one morphism, then there is an error somewhere since there should be only one morphism
            if prefix_to_power_set.len() > 1 {
                return Err(CalfErrors::MultipleMorphismsFromSuffixToPowerSet);
            }

            if prefix_to_power_set.is_empty() {
                if already_added {
                    return Err(CalfErrors::ErrorAddingPowersetMorphism);
                }
                // now we create a mapping from suffix to power set via membership query
                self.add_power_set_morphism(&self.prefix.clone()).await?;
                already_added = true;
                continue;
            }

            // here we have exactly one morphism from fs to power set and one from suffix to power set
            if prefix_to_power_set.len() == 1 {
                let morphism = prefix_to_power_set.into_iter().last().unwrap().clone();
                return Ok(morphism)
            }
            return Err(CalfErrors::UnknownError);
        }
    }

    async fn get_or_create_prefix_alphabet_to_powerset_morphism(&mut self) -> Result<Arc<Morphism<CategorySubObjectAlias<BaseCategory>>>, CalfErrors>
    {
        let mut already_added = false;
        loop {
            let prefix_alphabet_to_power_set =
                self.category.get_hom_set(&*self.prefix_alphabet.clone(), &*self.suffix_power_set).await?;

            // there is more than one morphism, then there is an error somewhere since there should be only one morphism
            if prefix_alphabet_to_power_set.len() > 1 {
                return Err(CalfErrors::MultipleMorphismsFromFSToPowerSet);
            }

            if prefix_alphabet_to_power_set.is_empty() {
                if already_added {
                    return Err(CalfErrors::ErrorAddingPowersetMorphism);
                }
                // now we create a mapping from fs to power set via membership query
                self.add_power_set_morphism(&self.prefix_alphabet.clone()).await?;
                already_added = true;
                continue;
            }

            // here we have exactly one morphism from fs to power set and one from suffix to power set
            if prefix_alphabet_to_power_set.len() == 1 {
                return Ok(prefix_alphabet_to_power_set.into_iter().last().unwrap().clone())
            }

            return Err(CalfErrors::UnknownError);
        }
    }

    async fn get_or_create_morphism_to_powerset(&mut self) -> Result<(
        Arc<Morphism<CategorySubObjectAlias<BaseCategory>>>,
        Arc<Morphism<CategorySubObjectAlias<BaseCategory>>>), CalfErrors>
    {

        let prefix_to_power_set_morphism = self.get_or_create_prefix_to_powerset_morphism().await?.clone();
        let prefix_alphabet_to_power_set = self.get_or_create_prefix_alphabet_to_powerset_morphism().await?.clone();

        Ok((prefix_to_power_set_morphism, prefix_alphabet_to_power_set))
    }


    pub async fn add_power_set_morphism(&mut self, object: &Arc<BaseCategory::Object>) -> Result<(), CalfErrors>
    {
        let mut mappings = HashMap::new();

        let suffix_objects = self.suffix.get_all_objects().await?;
        // map identity morphism first.
        for sub_object in object.get_all_objects().await? {
            let mut oracle_object = "".to_string();
            for suffix in &suffix_objects{
                let query = sub_object.category_id().to_owned() + suffix.category_id().clone();
                let query_result = self.oracle.membership_query(&query.to_string());
                oracle_object += &query_result.to_string();
            }
            // now find target object oracle object.
            println!("Mapping object {} to {}", sub_object.category_id(), oracle_object);
            println!("Suffix object");
            for s in self.suffix_power_set.get_all_objects().await?{
                println!(" - {}", s.category_id());
            }
            let target_object = self.suffix_power_set.get_object(&<String as Into<<BaseCategory::Object as CategoryTrait>::Object>>::into(oracle_object)).await?;
            let target_identity_morphism = self.suffix_power_set.get_identity_morphism(&**target_object).await?;
            mappings.insert(
                object.get_identity_morphism(&**sub_object).await?.clone(),
                target_identity_morphism.clone()
            );
        }

        // create a new morphism from object to power set
        let morphism = Morphism::new_with_mappings(
            object.clone(),
            self.suffix_power_set.clone(),
            mappings,
        );
        self.category.add_morphism(Arc::new(morphism)).await?;
        Ok(())
    }

    pub async fn update_table(
        &mut self,
        target_ref: &Arc<BaseCategory::Object>,
        morphisms: HashSet<Arc<<BaseCategory::Object as CategoryTrait>::Morphism>>,
    ) -> Result<Arc<BaseCategory::Object>, CalfErrors>{
        let mut objects = vec![];
        for morphism in morphisms {
            let new_object = morphism.source_object().clone();
            objects.push(new_object);
        }

        let inclusion_functor = inclusion_functor(
            target_ref.clone(), objects).await?;

        let new_data = inclusion_functor.target_object();
        self.category.add_object(new_data.clone()).await?;

        let morphism = Arc::new(Morphism::new(
            String::generate(),
            target_ref.clone(),
            new_data.clone(),
            Some(inclusion_functor.clone())
        ));

        self.category.add_morphism(morphism).await?;

        Ok(new_data.clone())
    }


    pub async fn export_cytoscape(&self, file_path: &str) -> Result<(), CalfErrors> {
        Ok(save_category_to_cytoscape_json_file(
            self.category.inner_category(),
            true,
            10,
            file_path.to_string(),
        ).await?)
    }
}


