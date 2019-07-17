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

pub type Span<'a> = nom_locate::LocatedSpanEx<&'a str, [u128; 10]>;

mod thread_context {

    use std::cell::RefCell;
    use std::collections::HashMap;

    pub struct ParserIndex {
        index: HashMap<&'static str, u32>,
        allocated: [u128; 10],
    }

    impl ParserIndex {
        pub fn get(&mut self, key: &'static str) -> Option<u32> {
            if let Some(x) = self.index.get(key) {
                Some(*x)
            } else {
                for i in 0..1280u32 {
                    let upper = (i / 128) as usize;
                    let lower = i % 128;
                    if ((self.allocated[upper] >> lower) & 1) == 0 {
                        let val = 1u128 << lower;
                        let mask = !(1u128 << lower);
                        self.allocated[upper] = (self.allocated[upper] & mask) | val;
                        self.index.insert(key, i);
                        return Some(i);
                    }
                }
                None
            }
        }
    }

    thread_local!(
        pub static PARSER_INDEX: RefCell<ParserIndex> = {
            RefCell::new(ParserIndex{index: HashMap::new(), allocated: [0;10]})
        }
    );
}
