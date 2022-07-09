#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;
use core::ops::{Index};

verus! {

seq_macro::seq!(N in 0..63 {
    pub struct VecArray64<A> {
        // Expands to Variant64, Variant65, ...
        #(
            pub val_~N: A,
        )*
    }
});

impl<A> VecArray64<A> {
    pub fn update(&mut self, i: usize, val: A) {
        //concat_idents!(self.val, i)
       self.val_0 = val;
    }
}


impl<A> Index<usize> for VecArray64<A> {
    type Output = A;
    fn index(&self, i: usize) -> &A {
        //concat_idents!(self.val, i)
        &self.val_0
    }
}

//#[verifier(external_body)]
pub struct Vec<#[verifier(strictly_positive)] A> {
    pub vec: VecArray64<A>,
    pub index: usize,
}

impl<A> Vec<A> {
    pub spec fn view(&self) -> Seq<A>;

    #[verifier(external_body)]
    pub fn init(&self, size: usize, val: A)
        ensures
            self.view() === Seq::empty(),
            self.view().len() == size,
            forall|i: usize| i < size ==>  (self.view().index(i) === val)
    {
    }

    #[verifier(external_body)]
    pub fn push(&mut self, value: A)
        ensures
            self.view() === old(self).view().push(value),
    {
        self.vec.update(self.index, value);
        self.index += 1;
    }

    #[verifier(external_body)]
    pub fn pop(&mut self)
        requires
            old(self).len() > 0,
        ensures
           self.len() == old(self).len()-1,
    {
        self.index = self.index - 1;
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
        self.vec.update(i, a);
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
