// rust_verify/tests/example.rs expect-failures

#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use pervasive::option::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::modes::*;

#[verifier(external)]
fn main() {
}

verus!{

// exmaple 0: conjunt
proof fn test_expansion_very_easy() 
{
  let x = 5;
  assert((x >= 0) && (x != 5));
  //                  ^^^^^^^
}


// example1: simple function inline
// 
// TODO: check the span of `&&&`
// spec fn is_good_integer(z: int) -> bool 
// {
//   &&& z >= 0
//   &&& z != 5
// }
spec fn is_good_integer(z: int) -> bool 
{
  z >= 0 && z != 5
//          ^^^^^^
}

proof fn test_expansion_easy() 
{
  let x = 5;
  assert(is_good_integer(x));
}



// example2: simple `match` inline
spec fn is_good_opt(opt: Option<int>) -> bool
{
  match opt {
    Option::Some(k) => k > 10,
    Option::None => true,
  }
}

proof fn test_expansion_match() {
  let x = Option::Some(5);
  let y = Option::Some(4);
  assert(is_good_opt(x));
}


}