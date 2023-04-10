use core::{borrow::Borrow, cmp::Ordering, mem::replace};

use ghost::phantom;

use crate::collection::{Entry, SuperTreeCollection, TreeCollection, VebTreeCollectionMarker};
use crate::key::{MaybeBorrowed, Owned, VebKey};
use crate::{RemoveResult, VebTree};

pub trait VebTreeMarker<K, V> {
    type Tree: VebTree<Key = K, Value = V>;
}

#[phantom]
pub struct TreeMarker<#[invariant] Summary, #[invariant] Children>;

impl<K, V, Summary, Children> VebTreeMarker<K, V> for TreeMarker<Summary, Children>
where
    K: VebKey,
    Summary: VebTreeMarker<K::High, ()>,
    Children: VebTreeCollectionMarker<K, V>,
    for<'a> <Summary::Tree as VebTree>::MinKey<'a>: Into<Owned<K::HValue<'a>>>,
    for<'a> <Summary::Tree as VebTree>::MaxKey<'a>: Into<Owned<K::HValue<'a>>>,
    for<'a> <Summary::Tree as VebTree>::EntryKey<'a>: Into<Owned<K::HValue<'a>>>,

    for<'a> <TCT<Children, K, V> as VebTree>::MinKey<'a>: Into<Owned<K::LValue<'a>>>,
    for<'a> <TCT<Children, K, V> as VebTree>::MaxKey<'a>: Into<Owned<K::LValue<'a>>>,
    for<'a> <TCT<Children, K, V> as VebTree>::EntryKey<'a>: Into<Owned<K::LValue<'a>>>,
{
    type Tree = Tree<K, V, Summary, Children>;
}

type TC<Children, K, V> =
    <<Children as VebTreeCollectionMarker<K, V>>::TreeCollection as SuperTreeCollection<K, V>>::TC;
type TCT<Children, K, V> =
    <<Children as VebTreeCollectionMarker<K, V>>::TreeCollection as SuperTreeCollection<K, V>>::Tree;

pub struct Tree<K, V, Summary, Children>
where
    K: VebKey,
    Summary: VebTreeMarker<K::High, ()>,
    Children: VebTreeCollectionMarker<K, V>,
{
    min: (K, V),
    data: Option<TreeData<Summary, Children, K, V>>,
}

struct TreeData<Summary, Children, K, V>
where
    K: VebKey,
    Summary: VebTreeMarker<K::High, ()>,
    Children: VebTreeCollectionMarker<K, V>,
{
    max: (K, V),
    children: Option<(Summary::Tree, TC<Children, K, V>)>,
}

impl<Summary, Children, K, V> VebTree for Tree<K, V, Summary, Children>
where
    K: VebKey,
    Summary: VebTreeMarker<K::High, ()>,
    Children: VebTreeCollectionMarker<K, V>,

    for<'a> <Summary::Tree as VebTree>::MinKey<'a>: Into<Owned<K::HValue<'a>>>,
    for<'a> <Summary::Tree as VebTree>::MaxKey<'a>: Into<Owned<K::HValue<'a>>>,
    for<'a> <Summary::Tree as VebTree>::EntryKey<'a>: Into<Owned<K::HValue<'a>>>,

    for<'a> <TCT<Children, K, V> as VebTree>::MinKey<'a>: Into<Owned<K::LValue<'a>>>,
    for<'a> <TCT<Children, K, V> as VebTree>::MaxKey<'a>: Into<Owned<K::LValue<'a>>>,
    for<'a> <TCT<Children, K, V> as VebTree>::EntryKey<'a>: Into<Owned<K::LValue<'a>>>,
{
    type Key = K;
    type Value = V;
    type MinKey<'a> = &'a K
    where (Self, K): 'a;
    type MaxKey<'a> = &'a K
    where (Self, K): 'a;
    type EntryKey<'a> = MaybeBorrowed<'a, K>
    where (Self, K): 'a;

    /// O(1)
    fn from_monad(key: K, val: V) -> Self {
        Self {
            min: (key, val),
            data: None,
        }
    }

    /// `O(1)`.
    fn into_monad(self) -> Result<(K, V), Self> {
        if self.is_monad() {
            Ok(self.min)
        } else {
            Err(self)
        }
    }

    /// O(1)
    fn is_monad(&self) -> bool {
        self.data.is_none()
    }

    /// O(1)
    fn min_val(&self) -> (&K, &V) {
        (&self.min.0, &self.min.1)
    }

    /// O(1)
    fn min_val_mut(&mut self) -> (&K, &mut V) {
        (&self.min.0, &mut self.min.1)
    }

    /// O(1)
    fn max_val(&self) -> (&K, &V) {
        self.data
            .as_ref()
            .map(|data| (&data.max.0, &data.max.1))
            .unwrap_or((&self.min.0, &self.min.1))
    }

    /// O(1)
    fn max_val_mut(&mut self) -> (&K, &mut V) {
        self.data
            .as_mut()
            .map(|data| (&data.max.0, &mut data.max.1))
            .unwrap_or((&self.min.0, &mut self.min.1))
    }

    /// O(lg lg K)
    fn find<Q>(&self, k: Q) -> Option<(MaybeBorrowed<K>, &V)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let children = match (k.borrow().cmp(&self.min.0), self.data.as_ref()) {
            (Ordering::Less, _) => return None,
            (Ordering::Equal, _) => {
                return Some((MaybeBorrowed::Borrowed(&self.min.0), &self.min.1))
            }
            (Ordering::Greater, None) => return None,
            (
                Ordering::Greater,
                Some(TreeData {
                    max,
                    children: None,
                }),
            ) => {
                if *k.borrow() == max.0 {
                    return Some((MaybeBorrowed::Borrowed(&max.0), &max.1));
                } else {
                    return None;
                }
            }
            (
                Ordering::Greater,
                Some(TreeData {
                    max,
                    children: Some((_, children)),
                }),
            ) => {
                if *k.borrow() == max.0 {
                    return Some((MaybeBorrowed::Borrowed(&max.0), &max.1));
                } else {
                    children
                }
            }
        };

        let (high, low) = K::split(k);

        // Try to find the child where `k` is expected to live (identified by `high`)
        // Then ask that node for the successor to `low`. This is expected to short circuit if `low` is outside the range of `child`
        let (low, val) = children.get(high.borrow())?.find(low)?;

        Some((MaybeBorrowed::Owned(K::join(high, low.into().0)), val))
    }

    /// O(lg lg K)
    fn find_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<K>, &mut V)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let children = match (k.borrow().cmp(&self.min.0), self.data.as_mut()) {
            (Ordering::Less, _) => return None,
            (Ordering::Equal, _) => {
                return Some((MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1))
            }
            (Ordering::Greater, None) => return None,
            (
                Ordering::Greater,
                Some(TreeData {
                    max,
                    children: None,
                }),
            ) => {
                if *k.borrow() == max.0 {
                    return Some((MaybeBorrowed::Borrowed(&max.0), &mut max.1));
                } else {
                    return None;
                }
            }
            (
                Ordering::Greater,
                Some(TreeData {
                    max,
                    children: Some((_, children)),
                }),
            ) => {
                if *k.borrow() == max.0 {
                    return Some((MaybeBorrowed::Borrowed(&max.0), &mut max.1));
                } else {
                    children
                }
            }
        };

        let (high, low) = K::split(k);

        // Try to find the child where `k` is expected to live (identified by `high`)
        // Then ask that node for the successor to `low`. This is expected to short circuit if `low` is outside the range of `child`
        let (low, val) = children.get_mut(high.borrow())?.find_mut(low)?;

        Some((MaybeBorrowed::Owned(K::join(high, low.into().0)), val))
    }

    /// O(lg lg K)
    fn predecessor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<K>, &V)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let data = match self.data.as_ref() {
            None if *k.borrow() <= self.min.0 => return None,
            None => return Some((MaybeBorrowed::Borrowed(&self.min.0), &self.min.1)),
            Some(data) => data,
        };

        let (summary, children) = match (k.borrow().cmp(&data.max.0), data.children.as_ref()) {
            (Ordering::Greater, _) => {
                return Some((MaybeBorrowed::Borrowed(&data.max.0), &data.max.1))
            }
            (Ordering::Equal, None) => {
                debug_assert!(*k.borrow() > self.min.0);
                return Some((MaybeBorrowed::Borrowed(&self.min.0), &self.min.1));
            }
            (Ordering::Equal, Some((summary, children))) => {
                debug_assert!(*k.borrow() > self.min.0);

                let (high, ()) = summary.max_val();
                let child = children.get(high.borrow()).unwrap();
                let (low, val) = child.max_val();
                return Some((
                    MaybeBorrowed::Owned(K::join(high.into().0, low.into().0)),
                    val,
                ));
            }
            (Ordering::Less, _) if *k.borrow() <= self.min.0 => return None,
            (Ordering::Less, None) => {
                return Some((MaybeBorrowed::Borrowed(&self.min.0), &self.min.1));
            }
            (Ordering::Less, Some((summary, children))) => (summary, children),
        };

        let (high, low) = K::split(k);

        // Try to find the child where `k` is expected to live (identified by `high`)
        // Then ask that node for the predecessor to `low`. This is expected to short circuit if `low` is outside the range of `child`
        let low = children
            .get(high.borrow())
            .and_then(|child| child.predecessor(low));
        if let Some((low, val)) = low {
            return Some((MaybeBorrowed::Owned(K::join(high, low.into().0)), val));
        }

        // If we didn't find it, find the predecessor to `high` in the summary and use the `min` of that node
        if let Some((high, ())) = summary.predecessor(high) {
            let child = children.get(high.borrow()).unwrap();
            let (low, val) = child.max_val();
            return Some((
                MaybeBorrowed::Owned(K::join(high.into().0, low.into().0)),
                val,
            ));
        }

        // If there are no predecessor to `high`, then use the max value for this node
        Some((MaybeBorrowed::Borrowed(&self.min.0), &self.min.1))
    }

    /// O(lg lg K)
    fn predecessor_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<K>, &mut V)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let data = match self.data.as_mut() {
            None if *k.borrow() <= self.min.0 => return None,
            None => return Some((MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1)),
            Some(data) => data,
        };

        let (summary, children) = match (k.borrow().cmp(&data.max.0), data.children.as_mut()) {
            (Ordering::Greater, _) => {
                return Some((MaybeBorrowed::Borrowed(&data.max.0), &mut data.max.1))
            }
            (Ordering::Equal, None) => {
                debug_assert!(*k.borrow() > self.min.0);
                return Some((MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1));
            }
            (Ordering::Equal, Some((summary, children))) => {
                debug_assert!(*k.borrow() > self.min.0);

                let (high, ()) = summary.max_val();
                let child = children.get_mut(high.borrow()).unwrap();
                let (low, val) = child.max_val_mut();
                return Some((
                    MaybeBorrowed::Owned(K::join(high.into().0, low.into().0)),
                    val,
                ));
            }
            (Ordering::Less, _) if *k.borrow() <= self.min.0 => return None,
            (Ordering::Less, None) => {
                return Some((MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1));
            }
            (Ordering::Less, Some((summary, children))) => (summary, children),
        };

        let (high, low) = K::split(k);

        // Try to find the child where `k` is expected to live (identified by `high`)
        // Then ask that node for the predecessor to `low`. This is expected to short circuit if `low` is outside the range of `child`
        {
            // FIXME: rust-lang/rust#106116
            // Remove this when core::ptr::from_mut is stabilized
            pub fn from_mut<T: ?Sized>(r: &mut T) -> *mut T {
                r
            }
            // FIXME: rust-lang/rust#43234
            // Remove this unsafe hack when NLL works
            let children = unsafe { &mut *from_mut(children) };

            let low = children
                .get_mut(high.borrow())
                .and_then(|child| child.predecessor_mut(low));
            if let Some((low, val)) = low {
                return Some((MaybeBorrowed::Owned(K::join(high, low.into().0)), val));
            }
        }

        // If we didn't find it, find the predecessor to `high` in the summary and use the `min` of that node
        if let Some((high, ())) = summary.predecessor(high) {
            let child = children.get_mut(high.borrow()).unwrap();
            let (low, val) = child.max_val_mut();
            return Some((
                MaybeBorrowed::Owned(K::join(high.into().0, low.into().0)),
                val,
            ));
        }

        // If there are no predecessor to `high`, then use the max value for this node
        Some((MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1))
    }

    /// O(lg lg K)
    fn successor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<K>, &V)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let (max, summary, children) = match (k.borrow().cmp(&self.min.0), self.data.as_ref()) {
            (Ordering::Less, _) => {
                return Some((MaybeBorrowed::Borrowed(&self.min.0), &self.min.1))
            }
            (_, None) => return None,
            (
                Ordering::Equal,
                Some(TreeData {
                    max,
                    children: None,
                }),
            ) => {
                debug_assert!(*k.borrow() < max.0);
                return Some((MaybeBorrowed::Borrowed(&max.0), &max.1));
            }
            (
                Ordering::Equal,
                Some(TreeData {
                    max: _max,
                    children: Some((summary, children)),
                }),
            ) => {
                debug_assert!(*k.borrow() < _max.0);
                let (high, ()) = summary.min_val();
                let child = children.get(high.borrow()).unwrap();
                let (low, val) = child.min_val();
                return Some((
                    MaybeBorrowed::Owned(K::join(high.into().0, low.into().0)),
                    val,
                ));
            }
            (_, Some(data)) if *k.borrow() >= data.max.0 => return None,
            (
                _,
                Some(TreeData {
                    max,
                    children: None,
                }),
            ) => return Some((MaybeBorrowed::Borrowed(&max.0), &max.1)),
            (
                _,
                Some(TreeData {
                    max,
                    children: Some((summary, children)),
                }),
            ) => (max, summary, children),
        };

        let (high, low) = K::split(k);

        // Try to find the child where `k` is expected to live (identified by `high`)
        // Then ask that node for the successor to `low`. This is expected to short circuit if `low` is outside the range of `child`
        let low = children
            .get(high.borrow())
            .and_then(|child| child.successor(low));
        if let Some((low, val)) = low {
            return Some((MaybeBorrowed::Owned(K::join(high, low.into().0)), val));
        }

        // If we didn't find it, find the successor to `high` in the summary and use the `min` of that node
        if let Some((high, ())) = summary.successor(high) {
            let child = children.get(high.borrow()).unwrap();
            let (low, val) = child.min_val();
            return Some((
                MaybeBorrowed::Owned(K::join(high.into().0, low.into().0)),
                val,
            ));
        }

        // If there are no successors to `high`, then use the max value for this node
        Some((MaybeBorrowed::Borrowed(&max.0), &max.1))
    }

    /// O(lg lg K)
    fn successor_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<K>, &mut V)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let (max, summary, children) = match (k.borrow().cmp(&self.min.0), self.data.as_mut()) {
            (Ordering::Less, _) => {
                return Some((MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1))
            }
            (_, None) => return None,
            (
                Ordering::Equal,
                Some(TreeData {
                    max,
                    children: None,
                }),
            ) => {
                debug_assert!(*k.borrow() < max.0);
                return Some((MaybeBorrowed::Borrowed(&max.0), &mut max.1));
            }
            (
                Ordering::Equal,
                Some(TreeData {
                    max: (_max, _),
                    children: Some((summary, children)),
                }),
            ) => {
                debug_assert!(k.borrow() < _max);
                let (high, ()) = summary.min_val();
                let child = children.get_mut(high.borrow()).unwrap();
                let (low, val) = child.min_val_mut();
                return Some((
                    MaybeBorrowed::Owned(K::join(high.into().0, low.into().0)),
                    val,
                ));
            }
            (_, Some(data)) if *k.borrow() >= data.max.0 => return None,
            (
                _,
                Some(TreeData {
                    max,
                    children: None,
                }),
            ) => return Some((MaybeBorrowed::Borrowed(&max.0), &mut max.1)),
            (
                _,
                Some(TreeData {
                    max,
                    children: Some((summary, children)),
                }),
            ) => (max, summary, children),
        };

        let (high, low) = K::split(k);

        // Try to find the child where `k` is expected to live (identified by `high`)
        // Then ask that node for the successor to `low`. This is expected to short circuit if `low` is outside the range of `child`
        {
            // FIXME: rust-lang/rust#106116
            // Remove this when core::ptr::from_mut is stabilized
            pub fn from_mut<T: ?Sized>(r: &mut T) -> *mut T {
                r
            }
            // FIXME: rust-lang/rust#43234
            // Remove this unsafe hack when NLL works
            let children = unsafe { &mut *from_mut(children) };

            let low = children
                .get_mut(high.borrow())
                .and_then(|child| child.successor_mut(low));
            if let Some((low, val)) = low {
                return Some((MaybeBorrowed::Owned(K::join(high, low.into().0)), val));
            }
            drop(low)
        }

        // If we didn't find it, find the successor to `high` in the summary and use the `min` of that node
        if let Some((high, ())) = summary.successor(high) {
            let child = children.get_mut(high.borrow()).unwrap();
            let (low, val) = child.min_val_mut();
            return Some((
                MaybeBorrowed::Owned(K::join(high.into().0, low.into().0)),
                val,
            ));
        }

        // If there are no successors to `high`, then use the max value for this node
        Some((MaybeBorrowed::Borrowed(&max.0), &mut max.1))
    }

    /// O(lg lg K)
    fn insert<Q>(&mut self, k: Q, v: V) -> Option<(K, V)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        // See if `k` should take the place of `min`. If so, swap them and store the previous `min` in subtrees
        let ((high, low), v, data) = match (k.borrow().cmp(&self.min.0), self.data.as_mut()) {
            (Ordering::Equal, _) => return Some(replace(&mut self.min, (k.into().0, v))),
            // Monad path
            (Ordering::Less, None) => {
                let max = replace(&mut self.min, (k.into().0, v));
                self.data = Some(TreeData {
                    max,
                    children: None,
                });
                return None;
            }
            (Ordering::Greater, None) => {
                let max = (k.into().0, v);
                self.data = Some(TreeData {
                    max,
                    children: None,
                });
                return None;
            }
            (Ordering::Less, Some(data)) => {
                let (k, v) = replace(&mut self.min, (k.into().0, v));
                let (k, v) = match data.max.0.cmp(&k) {
                    Ordering::Equal => return Some(replace(&mut data.max, (k, v))),
                    Ordering::Greater => replace(&mut data.max, (k, v)),
                    Ordering::Less => (k, v),
                };

                (K::split(k), v, data)
            }
            (Ordering::Greater, Some(data)) => match k.borrow().cmp(&data.max.0) {
                Ordering::Equal => return Some(replace(&mut data.max, (k.into().0, v))),
                Ordering::Greater => {
                    let (k, v) = replace(&mut data.max, (k.into().0, v));
                    (K::split(k), v, data)
                }
                Ordering::Less => (K::split(k), v, data),
            },
        };

        if let Some((summary, children)) = &mut data.children {
            match children.entry(high) {
                Entry::Occupied(entry) => {
                    let (high, child) = TC::<Children, K, V>::decompose(entry);
                    child
                        .insert(low.into().0, v)
                        .map(|(low, v)| (K::join(high, low.into()), v))
                }
                Entry::Vacant(entry) => {
                    summary.insert(TC::<Children, K, V>::key(&entry).clone(), ());
                    TC::<Children, K, V>::insert(entry, VebTree::from_monad(low.into().0, v));
                    None
                }
            }
        } else {
            let children =
                TC::<Children, K, V>::create(high.borrow(), VebTree::from_monad(low.into().0, v));
            let summary = <Summary::Tree as VebTree>::from_monad(high.into().0, ());
            data.children = Some((summary, children));
            None
        }
    }

    /// O(lg lg K)
    fn remove<Q>(&mut self, k: Q) -> RemoveResult<(K, V)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        if self.min.0 == *k.borrow() {
            return match self.remove_min() {
                None => RemoveResult::Monad,
                Some(k) => RemoveResult::Removed(k),
            };
        }
        return match self.data.take() {
            // Monad, but `k` not found
            None => RemoveResult::NotPresent,

            // Only max
            Some(TreeData {
                max,
                children: None,
            }) => {
                if max.0 == *k.borrow() {
                    // become monad if found
                    RemoveResult::Removed(max)
                } else {
                    // not found so revert
                    self.data = Some(TreeData {
                        max,
                        children: None,
                    });
                    RemoveResult::NotPresent
                }
            }

            Some(TreeData {
                max,
                children: Some((summary, mut children)),
            }) if max.0 == *k.borrow() => {
                // Start by looking for the largest subtree
                let (high, ()) = summary.max_val();
                // We should always find an entry, since we're starting from the summary
                let mut child = match children.entry(high.borrow()) {
                    Entry::Occupied(v) => v,
                    Entry::Vacant(_) => unreachable!(),
                };
                // Try to remove the smallest entry from the subtree
                let (low, val, empty) = TC::<Children, K, V>::deref(&mut child)
                    .remove_max()
                    .map(|(low, val)| (low, val, false))
                    // Or remove the subtree entirely if it's a monad
                    .unwrap_or_else(|| {
                        let result = TC::<Children, K, V>::remove(child);
                        let (low, val) = result.tree.into_monad().ok().expect("Expected monad");
                        (low, val, result.empty)
                    });

                let high = high.into().0;
                self.data = Some(TreeData {
                    max: (K::join(high, low.into()), val),
                    children: if empty {
                        None
                    } else {
                        Some((summary, children))
                    },
                });
                RemoveResult::Removed(max)
            }

            Some(TreeData {
                max,
                children: Some((summary, mut children)),
            }) => {
                let (high, low) = K::split(k);

                let (res, empty) = loop {
                    let (low, val, empty) = {
                        let mut child = match children.entry(high.borrow()) {
                            Entry::Occupied(v) => v,
                            Entry::Vacant(_) => break (RemoveResult::NotPresent, false),
                        };

                        match TC::<Children, K, V>::deref(&mut child).remove(low) {
                            RemoveResult::NotPresent => break (RemoveResult::NotPresent, false),
                            RemoveResult::Monad => {
                                let result = TC::<Children, K, V>::remove(child);
                                let (low, val) =
                                    result.tree.into_monad().ok().expect("Expected monad");
                                (low, val, result.empty)
                            }
                            RemoveResult::Removed((low, val)) => (low, val, false),
                        }
                    };

                    break (
                        RemoveResult::Removed((K::join(high, low.into()), val)),
                        empty,
                    );
                };

                self.data = Some(TreeData {
                    max,
                    children: if empty {
                        None
                    } else {
                        Some((summary, children))
                    },
                });
                return res;
            }
        };
    }

    /// O(lg lg K)
    fn remove_min(&mut self) -> Option<(K, V)> {
        match self.data.take() {
            // No data, return monad
            None => None,
            // Only max, so become monad
            Some(TreeData {
                max,
                children: None,
            }) => Some(replace(&mut self.min, max)),
            // Subtree, so extract a new `min` from the subtree
            Some(TreeData {
                max,
                children: Some((summary, mut children)),
            }) => {
                // Start by looking for the smallest subtree
                let (high, ()) = summary.min_val();
                // We should always find an entry, since we're starting from the summary
                let mut child = match children.entry(high.borrow()) {
                    Entry::Occupied(v) => v,
                    Entry::Vacant(_) => unreachable!(),
                };
                // Try to remove the smallest entry from the subtree
                let (low, val, empty) = TC::<Children, K, V>::deref(&mut child)
                    .remove_min()
                    .map(|(low, val)| (low, val, false))
                    // Or remove the subtree entirely if it's a monad
                    .unwrap_or_else(|| {
                        let result = TC::<Children, K, V>::remove(child);
                        let (low, val) = result.tree.into_monad().ok().expect("Expected monad");
                        (low, val, result.empty)
                    });

                let min = K::join(high.into().0, low.into());
                self.data = Some(TreeData {
                    max,
                    children: if empty {
                        None
                    } else {
                        Some((summary, children))
                    },
                });
                Some(replace(&mut self.min, (min, val)))
            }
        }
    }

    /// O(lg lg K)
    fn remove_max(&mut self) -> Option<(K, V)> {
        match self.data.take() {
            // No data, return monad
            None => None,
            // Only max, so become monad
            Some(TreeData {
                max,
                children: None,
            }) => Some(max),
            // Subtree, so extract a new `min` from the subtree
            Some(TreeData {
                max,
                children: Some((summary, mut children)),
            }) => {
                // Start by looking for the largest subtree
                let (high, ()) = summary.max_val();
                // We should always find an entry, since we're starting from the summary
                let mut child = match children.entry(high.borrow()) {
                    Entry::Occupied(v) => v,
                    Entry::Vacant(_) => unreachable!(),
                };
                // Try to remove the smallest entry from the subtree
                let (low, val, empty) = TC::<Children, K, V>::deref(&mut child)
                    .remove_max()
                    .map(|(low, val)| (low, val, false))
                    // Or remove the subtree entirely if it's a monad
                    .unwrap_or_else(|| {
                        let result = TC::<Children, K, V>::remove(child);
                        let (low, val) = result.tree.into_monad().ok().expect("Expected monad");
                        (low, val, result.empty)
                    });

                let high = high.into().0;
                self.data = Some(TreeData {
                    max: (K::join(high, low.into()), val),
                    children: if empty {
                        None
                    } else {
                        Some((summary, children))
                    },
                });
                Some(max)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use core::fmt;

    use crate::{
        bitset::ByteSetMarker, hash::HashMapMarker, key::MaybeBorrowed, RemoveResult, VebTree,
    };

    use super::Tree;

    fn verify<K, V, T>(
        veb: &mut T,
        entry: fn(&K) -> T::EntryKey<'_>,
        finds: impl IntoIterator<Item = (K, Option<(K, V)>)>,
        predecessors: impl IntoIterator<Item = (K, Option<(K, V)>)>,
        successors: impl IntoIterator<Item = (K, Option<(K, V)>)>,
    ) where
        K: fmt::Debug + Clone,
        V: fmt::Debug + PartialEq,
        T: VebTree<Key = K, Value = V>,
        for<'a> T::EntryKey<'a>: fmt::Debug + PartialEq,
    {
        for (i, mut r) in finds {
            assert_eq!(
                veb.find(i.clone()),
                r.as_ref().map(|(k, v)| (entry(k), v)),
                "find {i:?}"
            );
            assert_eq!(
                veb.find_mut(i.clone()),
                r.as_mut().map(|(k, v)| (entry(k), v)),
                "find_mut {i:?}"
            );
        }
        for (i, mut r) in predecessors {
            assert_eq!(
                veb.predecessor(i.clone()),
                r.as_ref().map(|(k, v)| (entry(k), v)),
                "predecessor {i:?}"
            );
            assert_eq!(
                veb.predecessor_mut(i.clone()),
                r.as_mut().map(|(k, v)| (entry(k), v)),
                "predecessor_mut {i:?}"
            );
        }
        for (i, mut r) in successors {
            assert_eq!(
                veb.successor(i.clone()),
                r.as_ref().map(|(k, v)| (entry(k), v)),
                "successor {i:?}"
            );
            assert_eq!(
                veb.successor_mut(i.clone()),
                r.as_mut().map(|(k, v)| (entry(k), v)),
                "successor_mut {i:?}"
            );
        }
    }

    #[test]
    fn simple() {
        //VebTree
        type U16Tree = Tree<
            u16,           // Key
            &'static str,  // Value
            ByteSetMarker, // Summary
            // Children
            HashMapMarker<
                HashMapMarker, // Child "tree"
            >,
        >;
        fn entry<'a>(v: &'a u16) -> MaybeBorrowed<'a, u16> {
            MaybeBorrowed::Borrowed(v)
        }
        let mut v = U16Tree::from_monad(10, "a");

        assert_eq!(v.min_val(), (&10, &"a"));
        assert_eq!(v.max_val(), (&10, &"a"));
        verify::<_, _, U16Tree>(
            &mut v,
            entry,
            [
                (9, None),
                (10, Some((10, "a"))),
                (11, None),
                (12, None),
                (13, None),
                (14, None),
                (15, None),
                (16, None),
            ],
            [
                (9, None),
                (10, None),
                (11, Some((10, "a"))),
                (12, Some((10, "a"))),
                (13, Some((10, "a"))),
                (14, Some((10, "a"))),
                (15, Some((10, "a"))),
                (16, Some((10, "a"))),
            ],
            [
                (9, Some((10, "a"))),
                (10, None),
                (11, None),
                (12, None),
                (13, None),
                (14, None),
                (15, None),
                (16, None),
            ],
        );

        v.insert(15, "b");
        assert_eq!(v.min_val(), (&10, &"a"));
        assert_eq!(v.max_val(), (&15, &"b"));
        verify::<_, _, U16Tree>(
            &mut v,
            entry,
            [
                (9, None),
                (10, Some((10, "a"))),
                (11, None),
                (12, None),
                (13, None),
                (14, None),
                (15, Some((15, "b"))),
                (16, None),
            ],
            [
                (9, None),
                (10, None),
                (11, Some((10, "a"))),
                (12, Some((10, "a"))),
                (13, Some((10, "a"))),
                (14, Some((10, "a"))),
                (15, Some((10, "a"))),
                (16, Some((15, "b"))),
            ],
            [
                (9, Some((10, "a"))),
                (10, Some((15, "b"))),
                (11, Some((15, "b"))),
                (12, Some((15, "b"))),
                (13, Some((15, "b"))),
                (14, Some((15, "b"))),
                (15, None),
                (16, None),
            ],
        );

        v.insert(13, "c");
        assert_eq!(v.min_val(), (&10, &"a"));
        assert_eq!(v.max_val(), (&15, &"b"));
        verify::<_, _, U16Tree>(
            &mut v,
            entry,
            [
                (9, None),
                (10, Some((10, "a"))),
                (11, None),
                (12, None),
                (13, Some((13, "c"))),
                (14, None),
                (15, Some((15, "b"))),
                (16, None),
            ],
            [
                (9, None),
                (10, None),
                (11, Some((10, "a"))),
                (12, Some((10, "a"))),
                (13, Some((10, "a"))),
                (14, Some((13, "c"))),
                (15, Some((13, "c"))),
                (16, Some((15, "b"))),
            ],
            [
                (9, Some((10, "a"))),
                (10, Some((13, "c"))),
                (11, Some((13, "c"))),
                (12, Some((13, "c"))),
                (13, Some((15, "b"))),
                (14, Some((15, "b"))),
                (15, None),
                (16, None),
            ],
        );

        v.insert(14, "d");
        assert_eq!(v.remove(14), RemoveResult::Removed((14, "d")));
        verify::<_, _, U16Tree>(
            &mut v,
            entry,
            [
                (9, None),
                (10, Some((10, "a"))),
                (11, None),
                (12, None),
                (13, Some((13, "c"))),
                (14, None),
                (15, Some((15, "b"))),
                (16, None),
            ],
            [
                (9, None),
                (10, None),
                (11, Some((10, "a"))),
                (12, Some((10, "a"))),
                (13, Some((10, "a"))),
                (14, Some((13, "c"))),
                (15, Some((13, "c"))),
                (16, Some((15, "b"))),
            ],
            [
                (9, Some((10, "a"))),
                (10, Some((13, "c"))),
                (11, Some((13, "c"))),
                (12, Some((13, "c"))),
                (13, Some((15, "b"))),
                (14, Some((15, "b"))),
                (15, None),
                (16, None),
            ],
        );

        assert_eq!(v.remove(15), RemoveResult::Removed((15, "b")));
        assert_eq!(v.min_val(), (&10, &"a"));
        assert_eq!(v.max_val(), (&13, &"c"));
        verify::<_, _, U16Tree>(
            &mut v,
            entry,
            [
                (9, None),
                (10, Some((10, "a"))),
                (11, None),
                (12, None),
                (13, Some((13, "c"))),
                (14, None),
                (15, None),
                (16, None),
            ],
            [
                (9, None),
                (10, None),
                (11, Some((10, "a"))),
                (12, Some((10, "a"))),
                (13, Some((10, "a"))),
                (14, Some((13, "c"))),
                (15, Some((13, "c"))),
                (16, Some((13, "c"))),
            ],
            [
                (9, Some((10, "a"))),
                (10, Some((13, "c"))),
                (11, Some((13, "c"))),
                (12, Some((13, "c"))),
                (13, None),
                (14, None),
                (15, None),
                (16, None),
            ],
        );
    }
}
