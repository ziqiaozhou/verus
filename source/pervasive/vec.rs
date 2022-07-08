#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;

verus! {

seq_macro::seq!(N in 0..63 {
    struct VecArray64<#[verifier(strictly_positive)] A> {
        // Expands to Variant64, Variant65, ...
        #(
            val~N: A,
        )*
    }
});

impl<A> VecArray64<A> {
    fn new() -> Self {
        seq_macro::seq!(N in 0..63 {
            VecArray64 {
                // Expands to Variant64, Variant65, ...
                #(
                    val~N: 0 as A,
                )*
            }
        })
    }
}

    
#[verifier(external_body)]
pub struct Vec<#[verifier(strictly_positive)] A> {
    pub vec: VecArray64,
    pub index: usize,
}

impl<A> Vec<A> {
    pub spec fn view(&self) -> Seq<A>;

    #[verifier(external_body)]
    pub fn new() -> (v: Self)
        ensures
            v.view() === Seq::empty(),
    {
        Vec { vec: VecArray64::new(), index: 0 }
    }
    
    pub fn empty() -> (v: Self)
        ensures
            v.view() === Seq::empty(),
    {
        Vec::new()
    }

    #[verifier(external_body)]
    pub fn push(&mut self, value: A)
        ensures
            self.view() === old(self).view().push(value),
    {
        self.vec[self.index] = value;
    }

    #[verifier(external_body)]
    pub fn pop(&mut self) -> (value: A)
        requires
            old(self).len() > 0,
        ensures
            value === old(self).view().index(old(self).view().len() as int - 1),
            self.view() === old(self).view().subrange(0, old(self).view().len() as int - 1),
    {
        self.index = self.index - 1
        self.vec[self.index+1]
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn index(&self, i: usize) -> (r: &A)
        requires
            i < self.view().len(),
        ensures
            *r === self.view().index(i),
    {
        &self.vec[i]
    }

    #[verifier(external_body)]
    pub fn set(&mut self, i: usize, a: A)
        requires
            i < old(self).view().len(),
        ensures
            self.view() === old(self).view().update(i, a),
    {
        self.vec[i] = a;
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.view().len(),
    {
        self.index + 1
    }
}

} // verus!
