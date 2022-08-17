#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[allow(unused_imports)]

#[is_variant]
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
}
