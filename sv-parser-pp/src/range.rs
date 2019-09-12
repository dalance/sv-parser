use std::cmp::Ordering;

#[derive(Copy, Clone, Debug, Eq)]
pub struct Range {
    pub begin: usize,
    pub end: usize,
}

impl Range {
    pub fn new(begin: usize, end: usize) -> Self {
        assert!(begin < end);
        Range { begin, end }
    }

    pub fn offset(&mut self, offset: usize) {
        self.begin += offset;
        self.end += offset;
    }
}

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
