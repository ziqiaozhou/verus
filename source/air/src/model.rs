//! Provides an AIR-level interface to the model returned by the SMT solver
//! when it reaches a SAT/Unknown conclusion

use crate::ast::{Binders, Decl, DeclX, Ident, Snapshot, Snapshots, Typ, TypX};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub type SMTModelDef = Arc<SMTModelDefX>;
pub type SMTModelDefs = Arc<Vec<SMTModelDef>>;
/// Represent (define-fun f (...parameters...) return-type body) from SMT model
/// (This includes constants, which have an empty parameter list.)
// ignore `define-funcs-rec` and `define-fun-rec` (for now).
#[derive(Debug)]
pub struct SMTModelDefX {
    pub name: Ident,
    pub params: Option<Binders<Typ>>, // if None, constant
    pub return_type: Typ,
    pub body: Arc<String>,
}

// AIR-level expression with concrete value
// Note that AIR-level types are boolean/integer/func(lambda)/datatype(named)/bitvector (see air/ast.rs)

#[derive(Debug)]
pub enum ModelConstant {
    Bool(bool),
    Int(Arc<String>),
    Datatype(Arc<String>),
    //TODO
    // BitVec(Arc<String>, u32),
}

pub type ModelDef = Arc<ModelDefX>;
pub type ModelDefs = Arc<Vec<ModelDef>>;
#[derive(Debug)]
pub struct ModelDefX {
    pub name: Ident,
    pub typ: Typ,
    pub value: ModelConstant,
}

#[derive(Clone, Debug)]
/// AIR-level model of a concrete counterexample
pub struct Model {
    /// AIR-level counter example, must call [build()] to populate this
    pub model: HashMap<Ident, ModelDef>,
    /// Internal mapping of snapshot IDs to snapshots that map AIR variables to usage counts.
    /// Generated when converting mutable variables to Z3-level constants.
    pub id_snapshots: Snapshots, // Snapshots map sid to a snapshot; a Snapshot maps a variable name to the encoding number
    /// The list of parameter/local_vars of the function
    pub local_vars: HashSet<Ident>, // get more info
    /// types
    pub types: HashMap<Ident, Arc<TypX>>,
    /// The model that Z3 returns
    pub smt_model: HashMap<Ident, SMTModelDef>,
}

impl Model {
    /// Returns an (unpopulated) AIR model object.  Must call [build()] to fully populate.
    /// # Arguments
    /// * `model` - The model that Z3 returns
    /// * `snapshots` - Internal mapping of snapshot IDs to snapshots that map AIR variables to usage counts.
    pub fn new(snapshots: Snapshots, locals: Vec<Decl>) -> Model {
        let mut types = HashMap::new();

        // println!(
        //     "Note that air_model will be query specific. Creating a new model with {} snapshots",
        //     snapshots.len()
        // );

        let mut local_vars = HashSet::new();
        for var in locals {
            if let DeclX::Const(name, typ) = &*var {
                local_vars.insert(name.clone());
                types.insert(name.clone(), typ.clone());
            } else {
                panic!("debugger::local_vars, non-const")
            }
        }

        for (sid, snapshot) in &snapshots {
            println!("air model, sid: {:?}", sid);
            println!("air model, snapshot: {:?}", snapshot);
        }

        Model {
            model: HashMap::new(),
            id_snapshots: snapshots,
            local_vars,
            types,
            smt_model: HashMap::new(),
        }
    }

    pub fn translate_variable(&self, name: &Ident, sid: &Ident) -> Option<Ident> {
        // look for variable in the snapshot first
        let id_snapshot =
            &self.id_snapshots.get(sid).expect(format!("Cannot find snapshot: {:?}", sid).as_str());
        println!("Air Model:: translate variable: id_snapshot, {:?}", id_snapshot);
        if let Some(var_label) = id_snapshot.get(name) {
            // println!("Air Model:: translate variable: var_lable, {:?}", var_label);
            return Some(Arc::new(crate::var_to_const::rename_var(name, *var_label)));
        }
        None
    }

    // Produce a merged snapshot, push this to
    // policy:
    //       if two snapshot contain a same variable, prefer the bigger number for that variable
    //       for variables that are only present in one snapshot, safely merge those
    // For example, `snap%PRE` and `0_entry` will be better if these are merged, since both are for the initial state
    pub fn produce_merged_snapshot(&mut self, sid1: &Ident, sid2: &Ident, new_sid: &Ident) {
        let s1 = self
            .id_snapshots
            .get(sid1)
            .expect(format!("Cannot find snapshot: {:?}", sid1).as_str());
        let s2 = self
            .id_snapshots
            .get(sid2)
            .expect(format!("Cannot find snapshot: {:?}", sid2).as_str());

        let mut new_snapshot: Snapshot = HashMap::new();
        for (id1, suffix1) in s1 {
            new_snapshot.insert(id1.clone(), *suffix1);
        }

        for (id2, suffix2) in s2 {
            let chosen_suffix: u32 = if new_snapshot.contains_key(id2) {
                let suffix1 = new_snapshot.get(id2).unwrap();
                if suffix1 > suffix2 { *suffix1 } else { *suffix2 }
            } else {
                *suffix2
            };
            new_snapshot.insert(id2.clone(), chosen_suffix);
        }

        self.id_snapshots.insert(new_sid.clone(), new_snapshot);
    }

    // build self.model
    // for now, just build for `local_vars`
    // pub fn build(&mut self, context: &mut crate::context::Context) {
    //     if self.smt_model.len() == 0 || self.model.len() > 0 {
    //         panic! {"Air model build precondition not satisfied"}
    //     }

    //     for var in &self.local_vars {
    //         println!("Building {:?}", var);
    //         let typ = self.types.get(var).expect("Internal error: debugger type and local_vars");
    //         let smt_def =
    //             self.smt_model.get(var).expect("Internal error: debugger smt_model and local_vars");
    //         let body = &smt_def.body;

    //         // let expr = Node::Atom(var.to_string());
    //         // let result = context.eval_expr(expr);   // evaluate this var in current model in Z3
    //         // println!("{:?}", result);

    //         let value = match &**typ {
    //             TypX::Bool => {
    //                 if **body == "true" {
    //                     ModelConstant::Bool(true)
    //                 } else if **body == "false" {
    //                     ModelConstant::Bool(false)
    //                 } else {
    //                     panic!("unexpected boolean value: {:?}", **body)
    //                 }
    //             }
    //             TypX::Int => ModelConstant::Int(body.clone()),
    //             TypX::Lambda => {
    //                 panic!("TODO: parser lambda, {:?}", body);
    //             }
    //             TypX::Named(_ident) => ModelConstant::Datatype(body.clone()),
    //             TypX::BitVec(_u32) => panic!("TODO: parser bitvec, {:?}", body),
    //         };
    //         let air_def = Arc::new(ModelDefX { name: var.clone(), typ: typ.clone(), value: value });
    //         self.model.insert(var.clone(), air_def);
    //     }
    // for dd in &self.model {
    //     println!("{:?}", dd);
    // }
    // }
}
