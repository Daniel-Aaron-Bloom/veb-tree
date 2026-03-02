//! Iterator implementation for VebTree

use crate::{key::MaybeBorrowed, VebTree};

/// An iterator over the key-value pairs of a [`VebTree`]
pub struct Iter<'a, V: VebTree> {
    data: Option<IterData<'a, V>>,
    emitted: usize,
}

enum IterData<'a, V: VebTree> {
    Start(&'a V),
    Front {
        prev_key: MaybeBorrowed<'a, V::Key>,
        tree: &'a V,
    },
    Back {
        prev_key: MaybeBorrowed<'a, V::Key>,
        tree: &'a V,
    },
    Both {
        front_key: MaybeBorrowed<'a, V::Key>,
        back_key: MaybeBorrowed<'a, V::Key>,
        tree: &'a V,
    },
}

impl<'a, V: VebTree> From<&'a V> for Iter<'a, V> {
    fn from(v: &'a V) -> Self {
        Self {
            data: Some(IterData::Start(v)),
            emitted: 0,
        }
    }
}

impl<'a, V: VebTree> Iterator for Iter<'a, V>
where
    V::Key: Clone,
{
    type Item = (MaybeBorrowed<'a, V::Key>, &'a V::Value);
    fn next(&mut self) -> Option<Self::Item> {
        use IterData::*;
        let v = match self.data.take()? {
            Start(tree) => {
                let (prev_key, val) = tree.min_val();
                self.data = Some(Front {
                    prev_key: prev_key.clone(),
                    tree,
                });
                (prev_key, val)
            }
            Front { prev_key, tree } => {
                if let Some((prev_key, val)) = tree.successor(prev_key) {
                    self.data = Some(Front {
                        prev_key: prev_key.clone(),
                        tree,
                    });
                    (prev_key, val)
                } else {
                    self.data = None;
                    return None;
                }
            }
            Back {
                prev_key: back_key,
                tree,
            } => {
                let (front_key, val) = tree.min_val();
                if front_key.borrow() == back_key.borrow() {
                    self.data = None;
                    return None;
                }
                self.data = Some(Both {
                    front_key: front_key.clone(),
                    back_key,
                    tree,
                });
                (front_key, val)
            }
            Both {
                front_key,
                back_key,
                tree,
            } => {
                if let Some((front_key, val)) = tree.successor(front_key) {
                    if front_key.borrow() == back_key.borrow() {
                        self.data = None;
                        return None;
                    }
                    self.data = Some(Both {
                        front_key: front_key.clone(),
                        back_key,
                        tree,
                    });
                    (front_key, val)
                } else {
                    // TODO: replace with unreachable after confidence
                    debug_assert!(false);
                    self.data = None;
                    return None;
                }
            }
        };
        self.emitted += 1;
        Some(v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        use IterData::*;
        match self.data {
            None => (0, Some(0)),
            Some(Start(tree) | Front { tree, .. } | Back { tree, .. } | Both { tree, .. }) => {
                let (min, max) = tree.len_hint();

                (
                    min.saturating_sub(self.emitted),
                    max.map(|max| max - self.emitted),
                )
            }
        }
    }
}

impl<'a, V: VebTree> DoubleEndedIterator for Iter<'a, V>
where
    V::Key: Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        use IterData::*;
        let v = match self.data.take()? {
            Start(tree) => {
                let (prev_key, val) = tree.max_val();
                self.data = Some(Back {
                    prev_key: prev_key.clone(),
                    tree,
                });
                (prev_key, val)
            }
            Back { prev_key, tree } => {
                if let Some((prev_key, val)) = tree.predecessor(prev_key) {
                    self.data = Some(Back {
                        prev_key: prev_key.clone(),
                        tree,
                    });
                    (prev_key, val)
                } else {
                    self.data = None;
                    return None;
                }
            }
            Front {
                prev_key: front_key,
                tree,
            } => {
                let (back_key, val) = tree.max_val();
                if front_key.borrow() == back_key.borrow() {
                    self.data = None;
                    return None;
                }
                self.data = Some(Both {
                    front_key,
                    back_key: back_key.clone(),
                    tree,
                });
                (back_key, val)
            }
            Both {
                front_key,
                back_key,
                tree,
            } => {
                if let Some((back_key, val)) = tree.predecessor(back_key) {
                    if front_key.borrow() == back_key.borrow() {
                        self.data = None;
                        return None;
                    }
                    self.data = Some(Both {
                        front_key,
                        back_key: back_key.clone(),
                        tree,
                    });
                    (back_key, val)
                } else {
                    // TODO: replace with unreachable after confidence
                    debug_assert!(false);
                    self.data = None;
                    return None;
                }
            }
        };
        self.emitted += 1;
        Some(v)
    }
}

impl<'a, V: VebTree> core::iter::FusedIterator for Iter<'a, V> where V::Key: Clone {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        markers::{Marker16, Marker32, VebTreeType},
        SizedVebTree,
    };
    use alloc::collections::BTreeMap;

    type U16Tree = VebTreeType<u16, i32, Marker16>;
    type U32Tree = VebTreeType<u32, &'static str, Marker32>;

    /// Helper to collect iterator into a vec
    fn collect_iter<V: VebTree>(tree: &V) -> alloc::vec::Vec<(V::Key, V::Value)>
    where
        V::Key: Clone,
        V::Value: Clone,
    {
        Iter::from(tree)
            .map(|(k, v)| (k.into_or_clone(), v.clone()))
            .collect()
    }

    #[test]
    fn iter_single_element() {
        let tree = SizedVebTree::<U16Tree>::from_monad(42, 100);
        let mut iter = Iter::from(&tree);

        // Check size_hint in Start state
        assert_eq!(iter.size_hint(), (1, Some(1)));

        // First call should yield the element
        let result = iter.next();
        assert_eq!(result, Some((MaybeBorrowed::Borrowed(&42), &100)));

        // size_hint after consuming one element
        assert_eq!(iter.size_hint(), (0, Some(0)));

        // Second call should be None
        assert_eq!(iter.next(), None);
        assert_eq!(iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn iter_single_element_backwards() {
        let tree = SizedVebTree::<U16Tree>::from_monad(42, 100);
        let mut iter = Iter::from(&tree);

        // Check size_hint in Start state
        assert_eq!(iter.size_hint(), (1, Some(1)));

        // First call to next_back should yield the element
        let result = iter.next_back();
        assert_eq!(result, Some((MaybeBorrowed::Borrowed(&42), &100)));

        // size_hint after consuming
        assert_eq!(iter.size_hint(), (0, Some(0)));

        // Second call should be None
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn iter_two_elements_forward() {
        let mut tree = SizedVebTree::<U16Tree>::from_monad(10, 1);
        tree.insert(20, 2);

        let mut iter = Iter::from(&tree);
        assert_eq!(iter.size_hint(), (2, Some(2)));

        // First element
        let result = iter.next();
        assert_eq!(result, Some((MaybeBorrowed::Borrowed(&10), &1)));
        assert_eq!(iter.size_hint(), (1, Some(1)));

        // Second element
        let result = iter.next();
        assert_eq!(result, Some((MaybeBorrowed::Borrowed(&20), &2)));
        assert_eq!(iter.size_hint(), (0, Some(0)));

        // Exhausted
        assert_eq!(iter.next(), None);
        assert_eq!(iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn iter_two_elements_backward() {
        let mut tree = U16Tree::from_monad(10, 1);
        tree.insert(20, 2);

        let mut iter = Iter::from(&tree);

        // Backward iteration
        let result = iter.next_back();
        assert_eq!(result, Some((MaybeBorrowed::Borrowed(&20), &2)));

        let result = iter.next_back();
        assert_eq!(result, Some((MaybeBorrowed::Borrowed(&10), &1)));

        // Exhausted
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn iter_state_transition_start_to_front() {
        let mut tree = U16Tree::from_monad(10, 1);
        tree.insert(20, 2);
        tree.insert(30, 3);

        let mut iter = Iter::from(&tree);

        // Start -> Front (via next)
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&10))
        );
        // Now in Front state
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&20))
        );
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&30))
        );
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_state_transition_start_to_back() {
        let mut tree = U16Tree::from_monad(10, 1);
        tree.insert(20, 2);
        tree.insert(30, 3);

        let mut iter = Iter::from(&tree);

        // Start -> Back (via next_back)
        assert_eq!(
            iter.next_back().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&30))
        );
        // Now in Back state
        assert_eq!(
            iter.next_back().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&20))
        );
        assert_eq!(
            iter.next_back().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&10))
        );
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn iter_state_transition_front_to_both() {
        let mut tree = U16Tree::from_monad(10, 1);
        tree.insert(20, 2);
        tree.insert(30, 3);
        tree.insert(40, 4);

        let mut iter = Iter::from(&tree);

        // Start -> Front
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&10))
        );
        // Front -> Both (via next_back)
        assert_eq!(
            iter.next_back().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&40))
        );
        // Now in Both state, continue from front
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&20))
        );
        // Continue from back
        assert_eq!(
            iter.next_back().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&30))
        );
        // Exhausted
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn iter_state_transition_back_to_both() {
        let mut tree = U16Tree::from_monad(10, 1);
        tree.insert(20, 2);
        tree.insert(30, 3);
        tree.insert(40, 4);

        let mut iter = Iter::from(&tree);

        // Start -> Back
        assert_eq!(
            iter.next_back().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&40))
        );
        // Back -> Both (via next)
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&10))
        );
        // Now in Both state
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&20))
        );
        assert_eq!(
            iter.next_back().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&30))
        );
        // Exhausted
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_alternating_directions() {
        let mut tree = U16Tree::from_monad(10, 1);
        tree.insert(20, 2);
        tree.insert(30, 3);
        tree.insert(40, 4);
        tree.insert(50, 5);

        let mut iter = Iter::from(&tree);

        // Mix forward and backward calls
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&10))
        );
        assert_eq!(
            iter.next_back().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&50))
        );
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&20))
        );
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&30))
        );
        assert_eq!(
            iter.next_back().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&40))
        );

        // All elements consumed
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn iter_meet_in_middle() {
        let mut tree = U16Tree::from_monad(10, 1);
        tree.insert(20, 2);
        tree.insert(30, 3);

        let mut iter = Iter::from(&tree);

        // Take from front
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&10))
        );
        // Take from back
        assert_eq!(
            iter.next_back().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&30))
        );
        // Take middle from front
        assert_eq!(
            iter.next().map(|(k, _)| k),
            Some(MaybeBorrowed::Borrowed(&20))
        );

        // Now they should meet
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn iter_size_hint_tracking() {
        let mut tree = SizedVebTree::<U16Tree>::from_monad(10, 1);
        tree.insert(20, 2);
        tree.insert(30, 3);
        tree.insert(40, 4);

        let mut iter = Iter::from(&tree);

        // Initial size hint (exact with SizedVebTree)
        assert_eq!(iter.size_hint(), (4, Some(4)));

        iter.next();
        assert_eq!(iter.size_hint(), (3, Some(3)));

        iter.next();
        assert_eq!(iter.size_hint(), (2, Some(2)));

        iter.next_back();
        assert_eq!(iter.size_hint(), (1, Some(1)));

        iter.next();
        assert_eq!(iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn iter_many_elements() {
        let mut tree = U16Tree::from_monad(0, 0);
        for i in 1..100 {
            tree.insert(i, i as i32);
        }

        let collected = collect_iter(&tree);
        assert_eq!(collected.len(), 100);

        // Verify ordering
        for (i, (k, v)) in collected.iter().enumerate() {
            assert_eq!(*k, i as u16);
            assert_eq!(*v, i as i32);
        }
    }

    #[test]
    fn iter_backwards_many_elements() {
        let mut tree = U16Tree::from_monad(0, 0);
        for i in 1..100 {
            tree.insert(i, i as i32);
        }

        let mut iter = Iter::from(&tree);
        let collected: alloc::vec::Vec<_> = iter
            .by_ref()
            .rev()
            .map(|(k, v)| (k.into_or_clone(), *v))
            .collect();

        assert_eq!(collected.len(), 100);

        // Verify reverse ordering
        for (i, (k, v)) in collected.iter().enumerate() {
            assert_eq!(*k, (99 - i) as u16);
            assert_eq!(*v, (99 - i) as i32);
        }
    }

    #[test]
    fn iter_both_state_correct_termination() {
        // Test that when front and back meet, iteration stops correctly
        let mut tree = U16Tree::from_monad(5, 5);
        tree.insert(10, 10);
        tree.insert(15, 15);
        tree.insert(20, 20);
        tree.insert(25, 25);

        let mut iter = Iter::from(&tree);

        // Consume from both ends until they meet
        assert_eq!(iter.next().map(|(k, _)| *k), Some(5));
        assert_eq!(iter.next_back().map(|(k, _)| *k), Some(25));
        assert_eq!(iter.next().map(|(k, _)| *k), Some(10));
        assert_eq!(iter.next_back().map(|(k, _)| *k), Some(20));

        // Middle element
        assert_eq!(iter.next().map(|(k, _)| *k), Some(15));

        // Should be exhausted now
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn iter_after_exhaustion() {
        let tree = U16Tree::from_monad(42, 100);
        let mut iter = Iter::from(&tree);

        // Consume the only element
        assert!(iter.next().is_some());

        // Multiple calls to next after exhaustion should all return None
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);

        // Same for next_back
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn iter_empty_after_removal() {
        let mut tree = U16Tree::from_monad(10, 1);
        tree.insert(20, 2);

        // Remove both elements
        let (tree, _) = tree.remove(10).ok().unwrap();
        let tree = tree.unwrap();
        let (tree, _) = tree.remove(20).ok().unwrap();

        // Tree should now be empty (None)
        assert!(tree.is_none());
    }

    #[test]
    fn sized_iter_exact_size() {
        let mut tree = SizedVebTree::<U16Tree>::from_monad(10, 1);
        tree.insert(20, 2);
        tree.insert(30, 3);

        let mut iter = Iter::from(&tree);

        // For SizedVebTree, size_hint should be exact
        assert_eq!(iter.size_hint(), (3, Some(3)));

        iter.next();
        assert_eq!(iter.size_hint(), (2, Some(2)));

        iter.next();
        assert_eq!(iter.size_hint(), (1, Some(1)));

        iter.next();
        assert_eq!(iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn btree_map_iter_compatibility() {
        // Test that BTreeMap (which implements VebTree) works with Iter
        let mut tree = BTreeMap::new();
        tree.insert(10u32, "ten");
        tree.insert(20u32, "twenty");
        tree.insert(30u32, "thirty");

        let mut iter = Iter::from(&tree);

        assert_eq!(iter.next().map(|(k, v)| (*k, *v)), Some((10, "ten")));
        assert_eq!(
            iter.next_back().map(|(k, v)| (*k, *v)),
            Some((30, "thirty"))
        );
        assert_eq!(iter.next().map(|(k, v)| (*k, *v)), Some((20, "twenty")));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_with_u32_keys() {
        let mut tree = U32Tree::from_monad(1000, "a");
        tree.insert(2000, "b");
        tree.insert(3000, "c");
        tree.insert(4000, "d");

        let collected = collect_iter(&tree);

        assert_eq!(collected.len(), 4);
        assert_eq!(collected[0], (1000, "a"));
        assert_eq!(collected[1], (2000, "b"));
        assert_eq!(collected[2], (3000, "c"));
        assert_eq!(collected[3], (4000, "d"));
    }

    #[test]
    fn iter_fused_property() {
        // Test that iterator remains None after exhaustion (fused iterator property)
        let tree = U16Tree::from_monad(42, 100);
        let mut iter = Iter::from(&tree);

        // Exhaust iterator
        while iter.next().is_some() {}

        // Should continue returning None
        for _ in 0..10 {
            assert_eq!(iter.next(), None);
        }
    }

    #[test]
    fn iter_values_correctness() {
        let mut tree = U16Tree::from_monad(5, 10);
        tree.insert(15, 30);
        tree.insert(10, 20);
        tree.insert(20, 40);

        let collected = collect_iter(&tree);

        // Should be in key order
        assert_eq!(
            collected,
            alloc::vec![(5, 10), (10, 20), (15, 30), (20, 40)]
        );
    }

    #[test]
    fn iter_single_next_after_next_back() {
        // Edge case: Start -> Back -> Front (changes direction)
        let mut tree = U16Tree::from_monad(10, 1);
        tree.insert(20, 2);

        let mut iter = Iter::from(&tree);

        // Start with next_back
        assert_eq!(iter.next_back().map(|(k, _)| *k), Some(20));
        // Then call next (should get the other element)
        assert_eq!(iter.next().map(|(k, _)| *k), Some(10));
        // Now exhausted
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_consumes_all_in_both_state() {
        let mut tree = U16Tree::from_monad(1, 1);
        for i in 2..=10 {
            tree.insert(i, i as i32);
        }

        let mut iter = Iter::from(&tree);

        // Enter Both state
        iter.next(); // 1
        iter.next_back(); // 10

        // Now consume all remaining from front
        let mut count = 1; // Already consumed 1 from front
        while iter.next().is_some() {
            count += 1;
        }

        // Should have consumed 9 more (2-9), since 10 was consumed from back
        assert_eq!(count, 9);
    }

    #[test]
    fn iter_mixed_pattern_stress() {
        // Stress test with various mixed patterns
        let mut tree = U16Tree::from_monad(0, 0);
        for i in 1..50 {
            tree.insert(i, i as i32);
        }

        let mut iter = Iter::from(&tree);
        let mut expected_front = 0u16;
        let mut expected_back = 49u16;

        // Alternate between front and back in various patterns
        for _ in 0..10 {
            assert_eq!(iter.next().map(|(k, _)| *k), Some(expected_front));
            expected_front += 1;

            assert_eq!(iter.next().map(|(k, _)| *k), Some(expected_front));
            expected_front += 1;

            assert_eq!(iter.next_back().map(|(k, _)| *k), Some(expected_back));
            expected_back -= 1;
        }

        // Consume remaining
        let remaining: alloc::vec::Vec<_> = iter.map(|(k, _)| *k).collect();
        let mut expected_remaining = alloc::vec::Vec::new();
        for i in expected_front..=expected_back {
            expected_remaining.push(i);
        }
        assert_eq!(remaining, expected_remaining);
    }
}
