use crate::parser::*;

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Locate {
    offset: usize,
    line: u32,
    len: usize,
}

impl<'a> From<Span<'a>> for Locate {
    fn from(x: Span<'a>) -> Self {
        Locate {
            offset: x.offset,
            line: x.line,
            len: x.fragment.len(),
        }
    }
}
