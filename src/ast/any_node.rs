use crate::ast::*;
use crate::parser::*;

// -----------------------------------------------------------------------------

include!(concat!(env!("OUT_DIR"), "/any_node.rs"));

pub struct AnyNodes<'a>(pub Vec<AnyNode<'a>>);

// -----------------------------------------------------------------------------

pub struct Iter<'a> {
    pub next: AnyNodes<'a>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = AnyNode<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let ret = self.next.0.pop();
        if let Some(x) = ret.clone() {
            let mut x = x.next();
            x.0.reverse();
            self.next.0.append(&mut x.0);
        }
        ret
    }
}

// -----------------------------------------------------------------------------

impl<'a> From<Vec<AnyNode<'a>>> for AnyNodes<'a> {
    fn from(x: Vec<AnyNode<'a>>) -> Self {
        AnyNodes(x)
    }
}

impl<'a> From<&'a Span<'a>> for AnyNodes<'a> {
    fn from(x: &'a Span<'a>) -> Self {
        vec![AnyNode::Span(x)].into()
    }
}

impl<'a, T: 'a> From<&'a Vec<T>> for AnyNodes<'a>
where
    &'a T: Into<AnyNodes<'a>>,
{
    fn from(x: &'a Vec<T>) -> Self {
        let mut ret = Vec::new();
        for x in x {
            ret.append(&mut x.into().0);
        }
        ret.into()
    }
}

impl<'a, T: 'a> From<&'a Option<T>> for AnyNodes<'a>
where
    &'a T: Into<AnyNodes<'a>>,
{
    fn from(x: &'a Option<T>) -> Self {
        let mut ret = Vec::new();
        if let Some(x) = x {
            ret.append(&mut x.into().0);
        }
        ret.into()
    }
}

impl<'a, T0: 'a> From<&'a (T0,)> for AnyNodes<'a>
where
    &'a T0: Into<AnyNodes<'a>>,
{
    fn from(x: &'a (T0,)) -> Self {
        let mut ret = Vec::new();
        let (t0,) = x;
        ret.append(&mut t0.into().0);
        ret.into()
    }
}

impl<'a, T0: 'a, T1: 'a> From<&'a (T0, T1)> for AnyNodes<'a>
where
    &'a T0: Into<AnyNodes<'a>>,
    &'a T1: Into<AnyNodes<'a>>,
{
    fn from(x: &'a (T0, T1)) -> Self {
        let mut ret = Vec::new();
        let (t0, t1) = x;
        ret.append(&mut t0.into().0);
        ret.append(&mut t1.into().0);
        ret.into()
    }
}

impl<'a, T0: 'a, T1: 'a, T2: 'a> From<&'a (T0, T1, T2)> for AnyNodes<'a>
where
    &'a T0: Into<AnyNodes<'a>>,
    &'a T1: Into<AnyNodes<'a>>,
    &'a T2: Into<AnyNodes<'a>>,
{
    fn from(x: &'a (T0, T1, T2)) -> Self {
        let mut ret = Vec::new();
        let (t0, t1, t2) = x;
        ret.append(&mut t0.into().0);
        ret.append(&mut t1.into().0);
        ret.append(&mut t2.into().0);
        ret.into()
    }
}

impl<'a, T0: 'a, T1: 'a, T2: 'a, T3: 'a> From<&'a (T0, T1, T2, T3)> for AnyNodes<'a>
where
    &'a T0: Into<AnyNodes<'a>>,
    &'a T1: Into<AnyNodes<'a>>,
    &'a T2: Into<AnyNodes<'a>>,
    &'a T3: Into<AnyNodes<'a>>,
{
    fn from(x: &'a (T0, T1, T2, T3)) -> Self {
        let mut ret = Vec::new();
        let (t0, t1, t2, t3) = x;
        ret.append(&mut t0.into().0);
        ret.append(&mut t1.into().0);
        ret.append(&mut t2.into().0);
        ret.append(&mut t3.into().0);
        ret.into()
    }
}

impl<'a, T0: 'a, T1: 'a, T2: 'a, T3: 'a, T4: 'a> From<&'a (T0, T1, T2, T3, T4)> for AnyNodes<'a>
where
    &'a T0: Into<AnyNodes<'a>>,
    &'a T1: Into<AnyNodes<'a>>,
    &'a T2: Into<AnyNodes<'a>>,
    &'a T3: Into<AnyNodes<'a>>,
    &'a T4: Into<AnyNodes<'a>>,
{
    fn from(x: &'a (T0, T1, T2, T3, T4)) -> Self {
        let mut ret = Vec::new();
        let (t0, t1, t2, t3, t4) = x;
        ret.append(&mut t0.into().0);
        ret.append(&mut t1.into().0);
        ret.append(&mut t2.into().0);
        ret.append(&mut t3.into().0);
        ret.append(&mut t4.into().0);
        ret.into()
    }
}

impl<'a, T0: 'a, T1: 'a, T2: 'a, T3: 'a, T4: 'a, T5: 'a> From<&'a (T0, T1, T2, T3, T4, T5)>
    for AnyNodes<'a>
where
    &'a T0: Into<AnyNodes<'a>>,
    &'a T1: Into<AnyNodes<'a>>,
    &'a T2: Into<AnyNodes<'a>>,
    &'a T3: Into<AnyNodes<'a>>,
    &'a T4: Into<AnyNodes<'a>>,
    &'a T5: Into<AnyNodes<'a>>,
{
    fn from(x: &'a (T0, T1, T2, T3, T4, T5)) -> Self {
        let mut ret = Vec::new();
        let (t0, t1, t2, t3, t4, t5) = x;
        ret.append(&mut t0.into().0);
        ret.append(&mut t1.into().0);
        ret.append(&mut t2.into().0);
        ret.append(&mut t3.into().0);
        ret.append(&mut t4.into().0);
        ret.append(&mut t5.into().0);
        ret.into()
    }
}

impl<'a, T0: 'a, T1: 'a, T2: 'a, T3: 'a, T4: 'a, T5: 'a, T6: 'a>
    From<&'a (T0, T1, T2, T3, T4, T5, T6)> for AnyNodes<'a>
where
    &'a T0: Into<AnyNodes<'a>>,
    &'a T1: Into<AnyNodes<'a>>,
    &'a T2: Into<AnyNodes<'a>>,
    &'a T3: Into<AnyNodes<'a>>,
    &'a T4: Into<AnyNodes<'a>>,
    &'a T5: Into<AnyNodes<'a>>,
    &'a T6: Into<AnyNodes<'a>>,
{
    fn from(x: &'a (T0, T1, T2, T3, T4, T5, T6)) -> Self {
        let mut ret = Vec::new();
        let (t0, t1, t2, t3, t4, t5, t6) = x;
        ret.append(&mut t0.into().0);
        ret.append(&mut t1.into().0);
        ret.append(&mut t2.into().0);
        ret.append(&mut t3.into().0);
        ret.append(&mut t4.into().0);
        ret.append(&mut t5.into().0);
        ret.append(&mut t6.into().0);
        ret.into()
    }
}

impl<'a, T0: 'a, T1: 'a, T2: 'a, T3: 'a, T4: 'a, T5: 'a, T6: 'a, T7: 'a>
    From<&'a (T0, T1, T2, T3, T4, T5, T6, T7)> for AnyNodes<'a>
where
    &'a T0: Into<AnyNodes<'a>>,
    &'a T1: Into<AnyNodes<'a>>,
    &'a T2: Into<AnyNodes<'a>>,
    &'a T3: Into<AnyNodes<'a>>,
    &'a T4: Into<AnyNodes<'a>>,
    &'a T5: Into<AnyNodes<'a>>,
    &'a T6: Into<AnyNodes<'a>>,
    &'a T7: Into<AnyNodes<'a>>,
{
    fn from(x: &'a (T0, T1, T2, T3, T4, T5, T6, T7)) -> Self {
        let mut ret = Vec::new();
        let (t0, t1, t2, t3, t4, t5, t6, t7) = x;
        ret.append(&mut t0.into().0);
        ret.append(&mut t1.into().0);
        ret.append(&mut t2.into().0);
        ret.append(&mut t3.into().0);
        ret.append(&mut t4.into().0);
        ret.append(&mut t5.into().0);
        ret.append(&mut t6.into().0);
        ret.append(&mut t7.into().0);
        ret.into()
    }
}

impl<'a, T0: 'a, T1: 'a, T2: 'a, T3: 'a, T4: 'a, T5: 'a, T6: 'a, T7: 'a, T8: 'a>
    From<&'a (T0, T1, T2, T3, T4, T5, T6, T7, T8)> for AnyNodes<'a>
where
    &'a T0: Into<AnyNodes<'a>>,
    &'a T1: Into<AnyNodes<'a>>,
    &'a T2: Into<AnyNodes<'a>>,
    &'a T3: Into<AnyNodes<'a>>,
    &'a T4: Into<AnyNodes<'a>>,
    &'a T5: Into<AnyNodes<'a>>,
    &'a T6: Into<AnyNodes<'a>>,
    &'a T7: Into<AnyNodes<'a>>,
    &'a T8: Into<AnyNodes<'a>>,
{
    fn from(x: &'a (T0, T1, T2, T3, T4, T5, T6, T7, T8)) -> Self {
        let mut ret = Vec::new();
        let (t0, t1, t2, t3, t4, t5, t6, t7, t8) = x;
        ret.append(&mut t0.into().0);
        ret.append(&mut t1.into().0);
        ret.append(&mut t2.into().0);
        ret.append(&mut t3.into().0);
        ret.append(&mut t4.into().0);
        ret.append(&mut t5.into().0);
        ret.append(&mut t6.into().0);
        ret.append(&mut t7.into().0);
        ret.append(&mut t8.into().0);
        ret.into()
    }
}

impl<'a, T0: 'a, T1: 'a, T2: 'a, T3: 'a, T4: 'a, T5: 'a, T6: 'a, T7: 'a, T8: 'a, T9: 'a>
    From<&'a (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)> for AnyNodes<'a>
where
    &'a T0: Into<AnyNodes<'a>>,
    &'a T1: Into<AnyNodes<'a>>,
    &'a T2: Into<AnyNodes<'a>>,
    &'a T3: Into<AnyNodes<'a>>,
    &'a T4: Into<AnyNodes<'a>>,
    &'a T5: Into<AnyNodes<'a>>,
    &'a T6: Into<AnyNodes<'a>>,
    &'a T7: Into<AnyNodes<'a>>,
    &'a T8: Into<AnyNodes<'a>>,
    &'a T9: Into<AnyNodes<'a>>,
{
    fn from(x: &'a (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)) -> Self {
        let mut ret = Vec::new();
        let (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) = x;
        ret.append(&mut t0.into().0);
        ret.append(&mut t1.into().0);
        ret.append(&mut t2.into().0);
        ret.append(&mut t3.into().0);
        ret.append(&mut t4.into().0);
        ret.append(&mut t5.into().0);
        ret.append(&mut t6.into().0);
        ret.append(&mut t7.into().0);
        ret.append(&mut t8.into().0);
        ret.append(&mut t9.into().0);
        ret.into()
    }
}

impl<
        'a,
        T0: 'a,
        T1: 'a,
        T2: 'a,
        T3: 'a,
        T4: 'a,
        T5: 'a,
        T6: 'a,
        T7: 'a,
        T8: 'a,
        T9: 'a,
        T10: 'a,
    > From<&'a (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)> for AnyNodes<'a>
where
    &'a T0: Into<AnyNodes<'a>>,
    &'a T1: Into<AnyNodes<'a>>,
    &'a T2: Into<AnyNodes<'a>>,
    &'a T3: Into<AnyNodes<'a>>,
    &'a T4: Into<AnyNodes<'a>>,
    &'a T5: Into<AnyNodes<'a>>,
    &'a T6: Into<AnyNodes<'a>>,
    &'a T7: Into<AnyNodes<'a>>,
    &'a T8: Into<AnyNodes<'a>>,
    &'a T9: Into<AnyNodes<'a>>,
    &'a T10: Into<AnyNodes<'a>>,
{
    fn from(x: &'a (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)) -> Self {
        let mut ret = Vec::new();
        let (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10) = x;
        ret.append(&mut t0.into().0);
        ret.append(&mut t1.into().0);
        ret.append(&mut t2.into().0);
        ret.append(&mut t3.into().0);
        ret.append(&mut t4.into().0);
        ret.append(&mut t5.into().0);
        ret.append(&mut t6.into().0);
        ret.append(&mut t7.into().0);
        ret.append(&mut t8.into().0);
        ret.append(&mut t9.into().0);
        ret.append(&mut t10.into().0);
        ret.into()
    }
}

impl<'a, T> From<&'a Paren<'a, T>> for AnyNodes<'a>
where
    &'a T: Into<AnyNodes<'a>>,
{
    fn from(x: &'a Paren<'a, T>) -> Self {
        let mut ret = Vec::new();
        let (a, b, c) = &x.nodes;
        let mut a: AnyNodes<'a> = a.into();
        let mut c: AnyNodes<'a> = c.into();
        ret.append(&mut a.0);
        ret.append(&mut b.into().0);
        ret.append(&mut c.0);
        ret.into()
    }
}

impl<'a, T> From<&'a Brace<'a, T>> for AnyNodes<'a>
where
    &'a T: Into<AnyNodes<'a>>,
{
    fn from(x: &'a Brace<'a, T>) -> Self {
        let mut ret = Vec::new();
        let (a, b, c) = &x.nodes;
        let mut a: AnyNodes<'a> = a.into();
        let mut c: AnyNodes<'a> = c.into();
        ret.append(&mut a.0);
        ret.append(&mut b.into().0);
        ret.append(&mut c.0);
        ret.into()
    }
}

impl<'a, T> From<&'a Bracket<'a, T>> for AnyNodes<'a>
where
    &'a T: Into<AnyNodes<'a>>,
{
    fn from(x: &'a Bracket<'a, T>) -> Self {
        let mut ret = Vec::new();
        let (a, b, c) = &x.nodes;
        let mut a: AnyNodes<'a> = a.into();
        let mut c: AnyNodes<'a> = c.into();
        ret.append(&mut a.0);
        ret.append(&mut b.into().0);
        ret.append(&mut c.0);
        ret.into()
    }
}

impl<'a, T> From<&'a ApostropheBrace<'a, T>> for AnyNodes<'a>
where
    &'a T: Into<AnyNodes<'a>>,
{
    fn from(x: &'a ApostropheBrace<'a, T>) -> Self {
        let mut ret = Vec::new();
        let (a, b, c) = &x.nodes;
        let mut a: AnyNodes<'a> = a.into();
        let mut c: AnyNodes<'a> = c.into();
        ret.append(&mut a.0);
        ret.append(&mut b.into().0);
        ret.append(&mut c.0);
        ret.into()
    }
}

impl<'a, T, U> From<&'a List<T, U>> for AnyNodes<'a>
where
    &'a T: Into<AnyNodes<'a>>,
    &'a U: Into<AnyNodes<'a>>,
{
    fn from(x: &'a List<T, U>) -> Self {
        let mut ret = Vec::new();
        let (t, u) = &x.nodes;
        let mut u: AnyNodes<'a> = u.into();
        ret.append(&mut t.into().0);
        ret.append(&mut u.0);
        ret.into()
    }
}

impl<'a, T: 'a> From<&'a Box<T>> for AnyNodes<'a>
where
    &'a T: Into<AnyNodes<'a>>,
{
    fn from(x: &'a Box<T>) -> Self {
        let mut ret = Vec::new();
        let mut x: AnyNodes<'a> = x.into();
        ret.append(&mut x.0);
        ret.into()
    }
}
