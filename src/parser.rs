#[macro_use]
pub mod utils;
pub use utils::*;

pub mod behavioral_statements;
pub mod declarations;
pub mod expressions;
pub mod general;
pub mod instantiations;
pub mod primitive_instances;
pub mod source_text;
pub mod specify_section;
pub mod udp_declaration_and_instantiation;
pub use behavioral_statements::*;
pub use declarations::*;
pub use expressions::*;
pub use general::*;
pub use instantiations::*;
pub use primitive_instances::*;
pub use source_text::*;
pub use specify_section::*;
pub use udp_declaration_and_instantiation::*;

pub type Span<'a> = nom_locate::LocatedSpanEx<&'a str, u128>;

// IDs for left recursion detection
//static REC_PRIMARY: u32 = 0;

mod thread_context {

    use std::cell::RefCell;
    use std::collections::HashMap;

    thread_local!(
        pub static MAP_MUT: RefCell<HashMap<(&'static str, &'static str, u32, u32), usize>> = {
            RefCell::new(HashMap::new())
        }
    );

    #[derive(Debug)]
    pub struct Table {
        index: HashMap<&'static str, u32>,
        offset: HashMap<&'static str, usize>,
        allocated: u128,
    }

    impl Table {
        pub fn get(&self, key: &'static str) -> Option<u32> {
            if let Some(x) = self.index.get(key) {
                Some(*x)
            } else {
                None
            }
        }

        pub fn get_or_allocate(&mut self, key: &'static str) -> Option<u32> {
            if let Some(x) = self.index.get(key) {
                Some(*x)
            } else {
                let allocated = self.allocated;
                for i in 0..128 {
                    if ((allocated >> i) & 1) == 0 {
                        let val = 1u128 << i;
                        let mask = !(1u128 << i);
                        self.allocated = (allocated & mask) | val;
                        self.index.insert(key, i);
                        return Some(i);
                    }
                }
                None
            }
        }

        pub fn release(&mut self, key: &'static str) {
            if let Some(x) = self.index.get(key) {
                let mask = !(1u128 << *x);
                self.allocated = self.allocated & mask;
                self.index.remove(key);
            }
        }
    }

    thread_local!(
        pub static TABLE: RefCell<Table> = {
            RefCell::new(Table{index: HashMap::new(), offset: HashMap::new(), allocated: 0})
        }
    );
}
