use sti::hash::HashMap;
use sti::vec::Vec;

use crate::env::SymbolId;


pub struct Traits {
    map: HashMap<SymbolId, Trait>,
}

struct Trait {
    impls: Vec<SymbolId>,
}

impl Traits {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    #[track_caller]
    pub fn new_trait(&mut self, symbol: SymbolId) {
        let prev = self.map.insert(symbol, Trait {
            impls: Vec::new(),
        });
        assert!(prev.is_none());
    }

    #[track_caller]
    pub fn add_impl(&mut self, trayt: SymbolId, impel: SymbolId) {
        self.map[&trayt].impls.push(impel);
    }

    pub fn is_trait(&self, symbol: SymbolId) -> bool {
        self.map.get(&symbol).is_some()
    }

    pub fn impls(&self, symbol: SymbolId) -> Option<&[SymbolId]> {
        if let Some(trayt) = &self.map.get(&symbol) {
            Some(&trayt.impls)
        }
        else { None }
    }
}

