use std::hash::Hash;
use std::collections::HashSet;
use std::marker::PhantomData;
use std::rc::Rc;
use uuid::Uuid;
use category_theory::core::traits::category_trait::CategoryTrait;
use category_theory::core::category::Category;
use category_theory::core::discrete_category::DiscreteCategory;
use category_theory::core::identifier::Identifier;
use category_theory::core::morphism::Morphism;
use category_theory::core::product_endofunctor::apply_product;
use category_theory::core::set_category::SetCategory;
use category_theory::core::traits::arrow_trait::ArrowTrait;
use category_theory::core::unit::unit_category::UnitCategory;
use crate::calf_errors::CalfErrors;
use crate::oracle_trait::{OracleTrait, QueryInputTrait};

pub struct CALF<
    OracleQuery: QueryInputTrait,
    Oracle: OracleTrait<OracleQuery>,
>
{
    category: Category<String, SetCategory<String>>,

    // holds all the prefix the last being the current suffix
    // s in L* algorithm
    prefix: Rc<SetCategory<String>>,

    // holds the suffixes of the last prefix
    // e in the L* algorithm
    suffix: Rc<SetCategory<String>>,

    alphabets: Rc<SetCategory<String>>,

    fsuffix: Rc<SetCategory<String>>,

    suffix_power_set: Rc<SetCategory<String>>,

    oracle: Oracle,

    _phantom: PhantomData<OracleQuery>
}


impl <
    OracleQuery: QueryInputTrait,
    Oracle: OracleTrait<OracleQuery>,
> CALF<OracleQuery, Oracle>
{
    pub fn new(alphabets: Rc<SetCategory<String>>, oracle: Oracle) -> Self {
        let mut category = Category::<String, SetCategory<String>>::new();
        // add alphabet object to the category
        category.add_object(alphabets.clone()).expect("Failed to add alphabet object");

        // add prefix and suffix with empty.
        let prefix: Rc<DiscreteCategory<String>> = Rc::new("".to_string().into());
        category.add_object(prefix.clone()).expect("Failed to add prefix");

        let suffix = Rc::new(SetCategory::new());
        category.add_object(suffix.clone()).expect("Failed to add suffix");

        let suffix_power_set = Rc::new(SetCategory::new());
        category.add_object(suffix_power_set.clone()).expect("Failed to add observations");


        let fsuffix = Rc::new(SetCategory::new());

        let mut result = CALF {
            category,
            prefix,
            suffix,
            alphabets,
            oracle,
            suffix_power_set,
            fsuffix,
            _phantom: PhantomData,
        };
        result.create_fsuffix();
        result
    }

    pub fn is_closed(&self) -> Result<bool, CalfErrors> {
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
        todo!()
    }


    pub fn is_consistent(&self) -> Result<bool, CalfErrors> {
        /*
        checks if the wrapper is consistent with the oracle
        i.e. for every (s,a) ∈ FS, there exists s′ ∈ S such that:
        FS(s,a) ∈ FS, there exists s′ ∈ S such that:

            (β∘δ∘Fα)(s,a)=(β∘α)(s′)

        then you can define:
            close W(s,a) = ew(s′) ∈ Hw
         */
        todo!()
    }

    pub fn run(&mut self) -> Result<(), CalfErrors> {
        loop {
            if !self.is_closed()? {
                self.make_closed()?;
                continue
            }
            if !self.is_consistent()? {
                self.make_consistent()?;
                continue
            }
            // if both closed and consistent, we can stop
            break;
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

    fn create_fsuffix(&mut self) {
        let fs = apply_product(self.prefix.clone(),
                               self.alphabets.clone()).expect("Failed to apply");

        // add the object to the category
        self.category.add_object(fs.target_object().clone())
            .expect("Failed to add product object to the category");

        self.fsuffix = fs.target_object().clone();
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

