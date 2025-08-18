pub trait QueryInputTrait: Clone {
    type Symbol: Clone + Eq;

    /// Concatenate / append a symbol (string case) or graft (tree case)
    fn append_symbol(&self, symbol: &Self::Symbol) -> Self;
}

/// Oracle for membership and equivalence queries
pub trait OracleTrait<W: QueryInputTrait + ?Sized> {
    fn membership_query(&self, input: &W) -> bool;

    fn equivalence_query<H: AutomatonTrait<W>>(
        &self,
        hypothesis: &H,
    ) -> Option<W>;
}

pub trait AutomatonTrait<I> {
    fn accepts(&self, word: &[I]) -> bool;
}

impl QueryInputTrait for String {
    type Symbol = ();

    fn append_symbol(&self, symbol: &Self::Symbol) -> Self {
        todo!()
    }
}