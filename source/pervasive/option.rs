#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;

#[is_variant]
#[derive(PartialEq, Eq, Structural)]
pub enum Option<A> {
    None,
    Some(A)
}

impl<A> Option<A> {
    #[spec]
    #[verifier(publish)]
    pub fn or(self, optb: Option<A>) -> Option<A> {
        match self {
            Option::None => optb,
            Option::Some(s) => self,
        }
    }

    #[spec]
    pub fn value(self) -> A {
        recommends(self.is_Some());
        self.get_Some_0()
    }
}
