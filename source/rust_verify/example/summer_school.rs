#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;

#[allow(unused_imports)]
use seq::*;
#[allow(unused_imports)]
use vec::*;

#[is_variant] #[derive(PartialEq, Eq)] // TODO(utaal): Structural is not implemented for Box
enum Tree {
    Nil,
    Node { value: i64, left: Box<Tree>, right: Box<Tree> },
}

impl Tree {
    #[spec] fn view(&self) -> Seq<int> {
        decreases(self);
        match *self {
            Tree::Nil => seq![],
            Tree::Node { value, left, right } => left.view().add(seq![value as int]).add(right.view()),
        }
    }

    #[spec] fn is_sorted(&self) -> bool {
        decreases(self);
        match *self {
            Tree::Nil => true,
            Tree::Node { value, left, right } => true
                && sequences_ordered_at_interface(left.view(), seq![value])
                && sequences_ordered_at_interface(seq![value], right.view())
                && left.is_sorted()
                && right.is_sorted()
        }
    }

    // #[proof] fn sorted_tree_means_sorted_sequence(&self) // TODO(utaal): is self being Spec too restrictive?
}

#[spec]
fn sequences_ordered_at_interface(seq1: Seq<int>, seq2: Seq<int>) -> bool {
    if seq1.len() == 0 || seq2.len() == 0 {
        true
    } else {
        seq1.last() <= seq2.index(0)
    }
}

#[spec] fn sequence_is_sorted(s: Seq<int>) -> bool {
    forall(|i: nat, j: nat| i < j && j < s.len() >>= s.index(i) <= s.index(j))
}

// TODO: change the default for --multiple-errors
// we can have --jon-mode :p
// TODO: shall multiple errors in the same method be sorted?
#[proof] fn sorted_tree_means_sorted_sequence(tree: Tree) {
    decreases(tree); // guessed by Dafny
    requires(tree.is_sorted());
    ensures(sequence_is_sorted(tree.view()));

    // reveal_with_fuel(sorted_tree_means_sorted_sequence, 3); // TODO(utaal) ICE revealing current method with fuel panics in AIR
    if let Tree::Node { left, right, value: _ } = tree {
        sorted_tree_means_sorted_sequence(*left); // guessed by Dafny
        sorted_tree_means_sorted_sequence(*right); // guessed by Dafny
    }
}

#[is_variant] #[derive(Eq, PartialEq, Structural)]
enum TreeSortedness {
    Unsorted,
    Empty,
    Bounded(i64, i64),
}

fn check_is_sorted_tree(tree: &Tree) -> TreeSortedness {
    decreases(tree);
    ensures(|ret: TreeSortedness| match ret {
        TreeSortedness::Unsorted => !tree.is_sorted(),
        TreeSortedness::Empty => tree.is_sorted() && tree.view().len() == 0,
        TreeSortedness::Bounded(l, r) => tree.is_sorted() && l == tree.view().index(0) && r == tree.view().last(),
    });

    match tree {
        Tree::Nil => TreeSortedness::Empty,
        Tree::Node { left, right, value } => {
            let left_sortedness = check_is_sorted_tree(left);
            let left_bound;
            match left_sortedness {
                TreeSortedness::Unsorted => return TreeSortedness::Unsorted,
                TreeSortedness::Empty => left_bound = *value,
                TreeSortedness::Bounded(ll, lr) => if !lr <= *value {
                    return TreeSortedness::Unsorted;
                } else {
                    left_bound = ll;
                },
            }

            let right_sortedness = check_is_sorted_tree(right);
            let right_bound;
            match right_sortedness {
                TreeSortedness::Unsorted => return TreeSortedness::Unsorted,
                TreeSortedness::Empty => right_bound = *value,
                TreeSortedness::Bounded(rl, rr) => if !*value <= rl {
                    return TreeSortedness::Unsorted;
                } else {
                    right_bound = rr;
                },
            }

            TreeSortedness::Bounded(left_bound, right_bound)
        }
    }
}


fn main() {}
