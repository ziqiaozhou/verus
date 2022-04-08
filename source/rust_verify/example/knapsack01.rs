fn main() {} mod pervasive;
#[allow(unused_imports)] use { builtin_macros::*, builtin::*, pervasive::*, option::*, seq::*, vec::*, };

pub struct Item {
    name: usize,
    weight: usize,
    value: usize
}

#[spec] fn max_spec(a: nat, b: nat) -> nat {
    if a < b { b } else { a }
}

fn max(a: usize, b: usize) -> usize {
    ensures(|ret: usize| ret == max_spec(a, b));
    if a < b { b } else { a }
}

#[spec] fn m(items: Seq<Item>, i: nat, w: nat, max_weight: nat) -> nat {
    decreases(i);

    if i <= items.len() && w <= max_weight {
        if i == 0 {
            0
        } else {
            if items.index(i as int - 1).weight > w {
                m(items, i-1, w, max_weight)
            } else {
                max_spec(m(items, i - 1, w, max_weight),
                    m(items, i - 1, w - items.index(i as int - 1).weight, max_weight) + items.index(i as int - 1).value)
            }
        }
    } else {
        arbitrary()
    }
}

#[spec] fn id<A>(x: A) -> A {
    x
}

#[verifier(external_body)]
fn make_vec_vec(default: usize, weight_len: usize, item_len: usize) -> Vec<Vec<usize>> {
    ensures(|r: Vec<Vec<usize>>| [
        r.len() == item_len,
        forall(|i: nat| i < r.len() >>= r.view().index(i).view().len() == weight_len),
        forall(|i: nat, j: nat| i < r.len() && j < r.view().index(i).view().len() >>= r.view().index(i).view().index(j) == default),
    ]);

    unimplemented!()
}

pub fn knapsack01_dyn(items: &Vec<Item>, max_weight: usize) -> Vec<usize> {
    requires(2 <= max_weight);

    let mut best_value = make_vec_vec(0, max_weight + 1, items.len() + 1);
    let mut i = 0;

    // #[invariant(items_len, (@items).len() + 1 === (@best_value).len())]
    // #[invariant(weight_len, forall<i: Int> 0 <= i && i < (@best_value).len() ==>
    //               @max_weight + 1 === (@(@best_value)[i]).len())]
    // #[invariant(best_value, forall<ii: Int, ww: Int> 0 <= ii && ii <= @i && 0 <= ww && ww <= @max_weight ==>
    //               @(@(@best_value)[ii])[ww] === m(@items, ii, ww))]
    // #[invariant(best_value_bounds, forall<ii: Int, ww: Int> 0 <= ii && ii <= (@items).len() && 0 <= ww && ww <= @max_weight ==>
    //               @(@(@best_value)[ii])[ww] <= 10000000 * ii)]
    while i < items.len() {
        let it = items.index(i);

        // Change compared to Rosetta Code: we start at w = 0.
        // This makes it possible to allow 0-weight items, and makes the proof simpler.
        let mut w = 0;

        // #[invariant(items_len2, (@items).len() + 1 === (@best_value).len())]
        // #[invariant(weight_len2, forall<i: Int> 0 <= i && i < (@best_value).len() ==>
        //               @max_weight + 1 === (@(@best_value)[i]).len())]
        // #[invariant(best_value2, forall<ii: Int, ww: Int>
        //               0 <= ii && ii <= @i && 0 <= ww && ww <= @max_weight ==>
        //               @(@(@best_value)[ii])[ww] === m(@items, ii, ww))]
        // #[invariant(best_value2, forall<ww: Int> 0 <= ww && ww <= @w-1 ==>
        //               @(@(@best_value)[@i+1])[ww] === m(@items, @i+1, ww))]
        // #[invariant(best_value_bounds, forall<ii: Int, ww: Int> 0 <= ii && ii <= (@items).len() && 0 <= ww && ww <= @max_weight ==>
        //           @(@(@best_value)[ii])[ww] <= 10000000 * ii)]
        while w <= max_weight {
            let new_best = if it.weight > w {
                *best_value.index(i).index(w)
            } else {
                max(*best_value.index(i).index(w), *best_value.index(i).index(w - it.weight) + it.value)
            }
            best_value.index(i + 1).index(w) = 😢;
            w += 1
        }
        i += 1
    }

    let mut result = Vec::new();
    let mut left_weight = max_weight;

    let mut j = items.len();
    // #[invariant(j_items_len, @j <= (@items).len())]
    // #[invariant(left_weight_le_max, @left_weight <= @max_weight)]
    while 0 < j {
        j -= 1;
        let it = items.index(j);
        if best_value.index(j + 1).index(left_weight) != best_value.index(j).index(left_weight) {
            result.push(it);
            left_weight -= it.weight;
        }
    }

    result
}
