use crate::*;
use core::convert::TryFrom;

// -----------------------------------------------------------------------------

include!(concat!(env!("OUT_DIR"), "/any_node.rs"));

pub struct RefNodes<'a>(pub Vec<RefNode<'a>>);

// -----------------------------------------------------------------------------

pub struct Iter<'a> {
    pub(crate) next: RefNodes<'a>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = RefNode<'a>;

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

impl<'a> From<Vec<RefNode<'a>>> for RefNodes<'a> {
    fn from(x: Vec<RefNode<'a>>) -> Self {
        RefNodes(x)
    }
}

impl<'a> From<&'a Locate> for RefNodes<'a> {
    fn from(x: &'a Locate) -> Self {
        vec![RefNode::Locate(x)].into()
    }
}

impl<'a, T: 'a> From<&'a Vec<T>> for RefNodes<'a>
where
    &'a T: Into<RefNodes<'a>>,
{
    fn from(x: &'a Vec<T>) -> Self {
        let mut ret = Vec::new();
        for x in x {
            ret.append(&mut x.into().0);
        }
        ret.into()
    }
}

impl<'a, T: 'a> From<&'a Option<T>> for RefNodes<'a>
where
    &'a T: Into<RefNodes<'a>>,
{
    fn from(x: &'a Option<T>) -> Self {
        let mut ret = Vec::new();
        if let Some(x) = x {
            ret.append(&mut x.into().0);
        }
        ret.into()
    }
}

impl<'a, T0: 'a> From<&'a (T0,)> for RefNodes<'a>
where
    &'a T0: Into<RefNodes<'a>>,
{
    fn from(x: &'a (T0,)) -> Self {
        let mut ret = Vec::new();
        let (t0,) = x;
        ret.append(&mut t0.into().0);
        ret.into()
    }
}

impl<'a, T0: 'a, T1: 'a> From<&'a (T0, T1)> for RefNodes<'a>
where
    &'a T0: Into<RefNodes<'a>>,
    &'a T1: Into<RefNodes<'a>>,
{
    fn from(x: &'a (T0, T1)) -> Self {
        let mut ret = Vec::new();
        let (t0, t1) = x;
        ret.append(&mut t0.into().0);
        ret.append(&mut t1.into().0);
        ret.into()
    }
}

impl<'a, T0: 'a, T1: 'a, T2: 'a> From<&'a (T0, T1, T2)> for RefNodes<'a>
where
    &'a T0: Into<RefNodes<'a>>,
    &'a T1: Into<RefNodes<'a>>,
    &'a T2: Into<RefNodes<'a>>,
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

impl<'a, T0: 'a, T1: 'a, T2: 'a, T3: 'a> From<&'a (T0, T1, T2, T3)> for RefNodes<'a>
where
    &'a T0: Into<RefNodes<'a>>,
    &'a T1: Into<RefNodes<'a>>,
    &'a T2: Into<RefNodes<'a>>,
    &'a T3: Into<RefNodes<'a>>,
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

impl<'a, T0: 'a, T1: 'a, T2: 'a, T3: 'a, T4: 'a> From<&'a (T0, T1, T2, T3, T4)> for RefNodes<'a>
where
    &'a T0: Into<RefNodes<'a>>,
    &'a T1: Into<RefNodes<'a>>,
    &'a T2: Into<RefNodes<'a>>,
    &'a T3: Into<RefNodes<'a>>,
    &'a T4: Into<RefNodes<'a>>,
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
    for RefNodes<'a>
where
    &'a T0: Into<RefNodes<'a>>,
    &'a T1: Into<RefNodes<'a>>,
    &'a T2: Into<RefNodes<'a>>,
    &'a T3: Into<RefNodes<'a>>,
    &'a T4: Into<RefNodes<'a>>,
    &'a T5: Into<RefNodes<'a>>,
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
    From<&'a (T0, T1, T2, T3, T4, T5, T6)> for RefNodes<'a>
where
    &'a T0: Into<RefNodes<'a>>,
    &'a T1: Into<RefNodes<'a>>,
    &'a T2: Into<RefNodes<'a>>,
    &'a T3: Into<RefNodes<'a>>,
    &'a T4: Into<RefNodes<'a>>,
    &'a T5: Into<RefNodes<'a>>,
    &'a T6: Into<RefNodes<'a>>,
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
    From<&'a (T0, T1, T2, T3, T4, T5, T6, T7)> for RefNodes<'a>
where
    &'a T0: Into<RefNodes<'a>>,
    &'a T1: Into<RefNodes<'a>>,
    &'a T2: Into<RefNodes<'a>>,
    &'a T3: Into<RefNodes<'a>>,
    &'a T4: Into<RefNodes<'a>>,
    &'a T5: Into<RefNodes<'a>>,
    &'a T6: Into<RefNodes<'a>>,
    &'a T7: Into<RefNodes<'a>>,
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
    From<&'a (T0, T1, T2, T3, T4, T5, T6, T7, T8)> for RefNodes<'a>
where
    &'a T0: Into<RefNodes<'a>>,
    &'a T1: Into<RefNodes<'a>>,
    &'a T2: Into<RefNodes<'a>>,
    &'a T3: Into<RefNodes<'a>>,
    &'a T4: Into<RefNodes<'a>>,
    &'a T5: Into<RefNodes<'a>>,
    &'a T6: Into<RefNodes<'a>>,
    &'a T7: Into<RefNodes<'a>>,
    &'a T8: Into<RefNodes<'a>>,
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
    From<&'a (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)> for RefNodes<'a>
where
    &'a T0: Into<RefNodes<'a>>,
    &'a T1: Into<RefNodes<'a>>,
    &'a T2: Into<RefNodes<'a>>,
    &'a T3: Into<RefNodes<'a>>,
    &'a T4: Into<RefNodes<'a>>,
    &'a T5: Into<RefNodes<'a>>,
    &'a T6: Into<RefNodes<'a>>,
    &'a T7: Into<RefNodes<'a>>,
    &'a T8: Into<RefNodes<'a>>,
    &'a T9: Into<RefNodes<'a>>,
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
    > From<&'a (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)> for RefNodes<'a>
where
    &'a T0: Into<RefNodes<'a>>,
    &'a T1: Into<RefNodes<'a>>,
    &'a T2: Into<RefNodes<'a>>,
    &'a T3: Into<RefNodes<'a>>,
    &'a T4: Into<RefNodes<'a>>,
    &'a T5: Into<RefNodes<'a>>,
    &'a T6: Into<RefNodes<'a>>,
    &'a T7: Into<RefNodes<'a>>,
    &'a T8: Into<RefNodes<'a>>,
    &'a T9: Into<RefNodes<'a>>,
    &'a T10: Into<RefNodes<'a>>,
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

impl<'a, T> From<&'a Paren<T>> for RefNodes<'a>
where
    &'a T: Into<RefNodes<'a>>,
{
    fn from(x: &'a Paren<T>) -> Self {
        let mut ret = Vec::new();
        let (a, b, c) = &x.nodes;
        let mut a: RefNodes<'a> = a.into();
        let mut c: RefNodes<'a> = c.into();
        ret.append(&mut a.0);
        ret.append(&mut b.into().0);
        ret.append(&mut c.0);
        ret.into()
    }
}

impl<'a, T> From<&'a Brace<T>> for RefNodes<'a>
where
    &'a T: Into<RefNodes<'a>>,
{
    fn from(x: &'a Brace<T>) -> Self {
        let mut ret = Vec::new();
        let (a, b, c) = &x.nodes;
        let mut a: RefNodes<'a> = a.into();
        let mut c: RefNodes<'a> = c.into();
        ret.append(&mut a.0);
        ret.append(&mut b.into().0);
        ret.append(&mut c.0);
        ret.into()
    }
}

impl<'a, T> From<&'a Bracket<T>> for RefNodes<'a>
where
    &'a T: Into<RefNodes<'a>>,
{
    fn from(x: &'a Bracket<T>) -> Self {
        let mut ret = Vec::new();
        let (a, b, c) = &x.nodes;
        let mut a: RefNodes<'a> = a.into();
        let mut c: RefNodes<'a> = c.into();
        ret.append(&mut a.0);
        ret.append(&mut b.into().0);
        ret.append(&mut c.0);
        ret.into()
    }
}

impl<'a, T> From<&'a ApostropheBrace<T>> for RefNodes<'a>
where
    &'a T: Into<RefNodes<'a>>,
{
    fn from(x: &'a ApostropheBrace<T>) -> Self {
        let mut ret = Vec::new();
        let (a, b, c) = &x.nodes;
        let mut a: RefNodes<'a> = a.into();
        let mut c: RefNodes<'a> = c.into();
        ret.append(&mut a.0);
        ret.append(&mut b.into().0);
        ret.append(&mut c.0);
        ret.into()
    }
}

impl<'a, T, U> From<&'a List<T, U>> for RefNodes<'a>
where
    &'a T: Into<RefNodes<'a>>,
    &'a U: Into<RefNodes<'a>>,
{
    fn from(x: &'a List<T, U>) -> Self {
        let mut ret = Vec::new();
        let (t, u) = &x.nodes;
        let mut u: RefNodes<'a> = u.into();
        ret.append(&mut t.into().0);
        ret.append(&mut u.0);
        ret.into()
    }
}

impl<'a, T: 'a> From<&'a Box<T>> for RefNodes<'a>
where
    &'a T: Into<RefNodes<'a>>,
{
    fn from(x: &'a Box<T>) -> Self {
        let mut ret = Vec::new();
        let mut x: RefNodes<'a> = (&**x).into();
        ret.append(&mut x.0);
        ret.into()
    }
}
