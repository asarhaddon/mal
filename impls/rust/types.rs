use std::cell::RefCell;
use dumpster::{Trace, unsync::Gc};
//use std::collections::HashMap;
use fnv::FnvHashMap;
use itertools::Itertools;

use crate::env::Env;
use crate::types::MalVal::{Bool, Func, Hash, Int, Kwd, List, MalFunc, Nil, Str, Sym, Vector};

#[derive(Clone, Trace)]
pub enum MalVal {
    Nil,
    Bool(bool),
    Int(i64),
    //Float(f64),
    Str(String),
    Sym(String),
    Kwd(String),
    List(Gc<Vec<MalVal>>, Gc<MalVal>),
    Vector(Gc<Vec<MalVal>>, Gc<MalVal>),
    Hash(Gc<FnvHashMap<String, MalVal>>, Gc<MalVal>),
    Func(fn(MalArgs) -> MalRet, Gc<MalVal>),
    MalFunc(FuncStruct),
    Atom(Gc<RefCell<MalVal>>),
}

#[derive(Clone, Trace)]
pub struct FuncStruct {
    pub ast: Gc<MalVal>,
    pub env: Env,
    pub params: Gc<MalVal>,
    pub is_macro: bool,
    pub meta: Gc<MalVal>,
}

pub type MalArgs = Vec<MalVal>;
pub type MalRet = Result<MalVal, MalVal>;

// type utility macros

macro_rules! list {
  [$($args:expr),*] => {{
    let v: Vec<MalVal> = vec![$($args),*];
    List(Gc::new(v),Gc::new(Nil))
  }}
}

// type utility functions

pub fn error<T>(s: &str) -> Result<T, MalVal> {
    Err(Str(s.to_string()))
}

pub fn list(seq: MalArgs) -> MalVal {
    List(Gc::new(seq), Gc::new(Nil))
}

pub fn vector(seq: MalArgs) -> MalVal {
    Vector(Gc::new(seq), Gc::new(Nil))
}

impl PartialEq for MalVal {
    fn eq(&self, other: &MalVal) -> bool {
        match (self, other) {
            (Nil, Nil) => true,
            (Bool(a), Bool(b)) => a == b,
            (Int(a), Int(b)) => a == b,
            (Str(a), Str(b)) => a == b,
            (Sym(a), Sym(b)) => a == b,
            (Kwd(a), Kwd(b)) => a == b,
            (List(a, _), List(b, _))
            | (Vector(a, _), Vector(b, _))
            | (List(a, _), Vector(b, _))
            | (Vector(a, _), List(b, _)) => a == b,
            (Hash(a, _), Hash(b, _)) => a == b,
            (MalFunc { .. }, MalFunc { .. }) => false,
            _ => false,
        }
    }
}

pub fn func(f: fn(MalArgs) -> MalRet) -> MalVal {
    Func(f, Gc::new(Nil))
}

pub fn _assoc(mut hm: FnvHashMap<String, MalVal>, kvs: MalArgs) -> MalRet {
    if kvs.len() % 2 != 0 {
        return error("odd number of elements");
    }
    for (k, v) in kvs.iter().tuples() {
        hm.insert(wrap_map_key(k)?, v.clone());
    }
    Ok(Hash(Gc::new(hm), Gc::new(Nil)))
}

pub fn wrap_map_key(k: &MalVal) -> Result<String, MalVal> {
    match k {
        Str(s) => Ok(String::from(s)),
        Kwd(s) => Ok(format!("\u{29e}{}", s)),
        _ => error("key is not string"),
    }
}

pub fn unwrap_map_key(s: &str) -> MalVal {
    match s.strip_prefix('\u{29e}') {
        Some(keyword) => Kwd(String::from(keyword)),
        _ => Str(String::from(s)),
    }
}

pub fn hash_map(kvs: MalArgs) -> MalRet {
    let hm: FnvHashMap<String, MalVal> = FnvHashMap::default();
    _assoc(hm, kvs)
}
