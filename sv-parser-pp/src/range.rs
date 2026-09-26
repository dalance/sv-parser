//! Half-open byte index range type with interval search ordering.
//!
//! This module provides [`Range`], representing a half-open interval `[begin, end)`.
//! [`Range`] implements a specialized [`PartialEq`] and [`Ord`] definition that treats
//! any two overlapping ranges as equal. This allows a [`std::collections::BTreeMap`]
//! keyed by non-overlapping [`Range`] entries to be queried for point containment
//! using `map.get(&Range::new(pos, pos + 1))` in O(log N) time.

use std::cmp::Ordering;

/// A half-open interval `[begin, end)` representing byte offsets within source text.
///
/// # Interval Query Behavior
///
/// `Range` implements [`PartialEq`] and [`Ord`] such that two ranges are considered equal
/// (`Ordering::Equal`) if they **overlap**. When stored as non-overlapping segments in a
/// [`std::collections::BTreeMap`], any point query `Range::new(pos, pos + 1)` will match
/// the segment `[begin, end)` containing `pos`.
#[derive(Copy, Clone, Debug, Eq)]
pub struct Range {
    /// Starting byte offset (inclusive).
    pub begin: usize,
    /// Ending byte offset (exclusive).
    pub end: usize,
}

impl Range {
    /// Creates a new `Range` covering `[begin, end)`.
    ///
    /// # Panics
    ///
    /// Panics if `begin > end`.
    pub fn new(begin: usize, end: usize) -> Self {
        assert!(begin <= end);
        Range { begin, end }
    }

    /// Shifts both `begin` and `end` offsets by the given `offset`.
    pub fn offset(&mut self, offset: usize) {
        self.begin += offset;
        self.end += offset;
    }
}

/// Evaluates whether two ranges overlap. Two ranges overlap if and only if
/// `max(self.begin, other.begin) < min(self.end, other.end)`.
impl PartialEq for Range {
    fn eq(&self, other: &Self) -> bool {
        if self.begin <= other.begin {
            other.begin < self.end
        } else {
            self.begin < other.end
        }
    }
}

impl Ord for Range {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.eq(other) {
            Ordering::Equal
        } else {
            self.begin.cmp(&other.begin)
        }
    }
}

impl PartialOrd for Range {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn test_btreemap() {
        let mut map = BTreeMap::new();
        map.insert(Range::new(0, 10), String::from("0-10"));
        map.insert(Range::new(10, 15), String::from("10-15"));
        assert_eq!(map.get(&Range::new(0, 1)), Some(&String::from("0-10")));
        assert_eq!(map.get(&Range::new(3, 4)), Some(&String::from("0-10")));
        assert_eq!(map.get(&Range::new(10, 11)), Some(&String::from("10-15")));
        assert_eq!(map.get(&Range::new(15, 16)), None);
    }
}
