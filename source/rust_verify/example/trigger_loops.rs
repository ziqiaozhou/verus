#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use pervasive::*;
mod pervasive;

fndecl!(fn f(x: nat, y: nat) -> bool);
fndecl!(fn g(x: nat) -> bool);

#[proof] 
fn choose_example() {
    requires (exists(|x| g(x)));

    let x = choose(|x| g(x));
    assert(g(x));
}

#[proof] 
fn trigger_forever() {
   requires(forall(|x: nat, y: nat| f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) >>= (#[trigger] f(x, y))));
   ensures(forall(|x: nat, y: nat| x > 2318 && y < 100 >>= f(x, y)));
}

#[exec]
fn bad_loop() {
    let mut x = 10;
    while (x > 10) {
        invariant(forall(|x: nat, y: nat| f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) >>= (#[trigger] f(x, y))));
        decreases(x);

        x = x - 1;
        assert(forall(|x: nat, y: nat| x > 2318 && y < 100 >>= f(x, y)));
    }
}

fn main() {}
