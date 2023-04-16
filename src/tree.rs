use core::{borrow::Borrow, cmp::Ordering, mem::replace};

use ghost::phantom;

use crate::collection::{SuperTreeCollection, TreeCollection, VebTreeCollectionMarker};
use crate::key::{MaybeBorrowed, VebKey};
use crate::VebTree;

pub trait VebTreeMarker<K, V> {
    type Tree: VebTree<Key = K, Value = V>;
}

#[phantom]
pub struct TreeMarker<#[invariant] Summary, #[invariant] Children>;

impl<K, V, Summary, Children> VebTreeMarker<K, V> for TreeMarker<Summary, Children>
where
    K: VebKey,
    Summary: VebTreeMarker<K::Hi, ()>,
    Children: VebTreeCollectionMarker<K, V>,
{
    type Tree = Tree<K, V, Summary, Children>;
}

type TC<Children, K, V> =
    <<Children as VebTreeCollectionMarker<K, V>>::TreeCollection as SuperTreeCollection<K, V>>::TC;

pub struct Tree<K, V, Summary, Children>
where
    K: VebKey,
    Summary: VebTreeMarker<K::Hi, ()>,
    Children: VebTreeCollectionMarker<K, V>,
{
    min: (K, V),
    data: Option<TreeData<Summary, Children, K, V>>,
}

struct TreeData<Summary, Children, K, V>
where
    K: VebKey,
    Summary: VebTreeMarker<K::Hi, ()>,
    Children: VebTreeCollectionMarker<K, V>,
{
    max: (K, V),
    children: Option<(Summary::Tree, TC<Children, K, V>)>,
}

impl<Summary, Children, K, V> Clone for TreeData<Summary, Children, K, V>
where
    K: VebKey + Clone,
    V: Clone,
    Summary: VebTreeMarker<K::Hi, ()>,
    Children: VebTreeCollectionMarker<K, V>,
    Option<(Summary::Tree, TC<Children, K, V>)>: Clone,
{
    fn clone(&self) -> Self {
        Self {
            max: self.max.clone(),
            children: self.children.clone(),
        }
    }
}
impl<K, V, Summary, Children> Clone for Tree<K, V, Summary, Children>
where
    K: VebKey + Clone,
    V: Clone,
    Summary: VebTreeMarker<K::Hi, ()>,
    Children: VebTreeCollectionMarker<K, V>,
    Option<TreeData<Summary, Children, K, V>>: Clone,
{
    fn clone(&self) -> Self {
        Self {
            min: self.min.clone(),
            data: self.data.clone(),
        }
    }
}

impl<Summary, Children, K, V> VebTree for Tree<K, V, Summary, Children>
where
    K: VebKey,
    Summary: VebTreeMarker<K::Hi, ()>,
    Children: VebTreeCollectionMarker<K, V>,
{
    type Key = K;
    type Value = V;

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
    fn min_val(&self) -> (MaybeBorrowed<K>, &V) {
        (MaybeBorrowed::Borrowed(&self.min.0), &self.min.1)
    }

    /// O(1)
    fn min_val_mut(&mut self) -> (MaybeBorrowed<K>, &mut V) {
        (MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1)
    }

    /// O(1)
    fn max_val(&self) -> (MaybeBorrowed<K>, &V) {
        let (k, v) = self
            .data
            .as_ref()
            .map(|data| (&data.max.0, &data.max.1))
            .unwrap_or((&self.min.0, &self.min.1));
        (MaybeBorrowed::Borrowed(k), v)
    }

    /// O(1)
    fn max_val_mut(&mut self) -> (MaybeBorrowed<K>, &mut V) {
        let (k, v) = self
            .data
            .as_mut()
            .map(|data| (&data.max.0, &mut data.max.1))
            .unwrap_or((&self.min.0, &mut self.min.1));
        (MaybeBorrowed::Borrowed(k), v)
    }

    /// O(lg lg K)
    fn find<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<K>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = k.into();
        use Ordering::*;
        match k.cmp(&self.min.0) {
            Less => return None,
            Equal => return Some((MaybeBorrowed::Borrowed(&self.min.0), &self.min.1)),
            Greater => {}
        }
        let data = match self.data.as_ref() {
            None => return None,
            Some(data) => data,
        };
        if *k.borrow() == data.max.0 {
            return Some((MaybeBorrowed::Borrowed(&data.max.0), &data.max.1));
        }
        let children = match &data.children {
            None => return None,
            Some((_, children)) => children,
        };

        K::split_ref(&*k, |hi, lo| {
            // Try to find the child where `k` is expected to live (identified by `hi`)
            // Then ask that node for the successor to `lo`. This is expected to short circuit if `lo` is outside the range of `child`
            let (lo, val) = children.get(hi)?.find(lo)?;

            Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val))
        })
    }

    /// O(lg lg K)
    fn find_mut<'a, Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<K>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = k.into();
        use Ordering::*;
        match k.borrow().cmp(&self.min.0) {
            Less => return None,
            Equal => return Some((MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1)),
            Greater => {}
        }
        let data = match self.data.as_mut() {
            None => return None,
            Some(data) => data,
        };
        if *k.borrow() == data.max.0 {
            return Some((MaybeBorrowed::Borrowed(&data.max.0), &mut data.max.1));
        }
        let children = match &mut data.children {
            None => return None,
            Some((_, children)) => children,
        };

        K::split_ref(&*k, |hi, lo| {
            // Try to find the child where `k` is expected to live (identified by `hi`)
            // Then ask that node for the successor to `lo`. This is expected to short circuit if `lo` is outside the range of `child`
            let (lo, val) = children.get_mut(&*hi)?.find_mut(lo)?;

            Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val))
        })
    }

    /// O(lg lg K)
    fn predecessor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<K>, &V)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = k.into();
        if *k.borrow() <= self.min.0 {
            return None;
        }
        let data = match self.data.as_ref() {
            None => return Some((MaybeBorrowed::Borrowed(&self.min.0), &self.min.1)),
            Some(data) => data,
        };

        let (summary, children) = match (k.borrow().cmp(&data.max.0), data.children.as_ref()) {
            (Ordering::Greater, _) => {
                return Some((MaybeBorrowed::Borrowed(&data.max.0), &data.max.1))
            }
            (_, None) => {
                return Some((MaybeBorrowed::Borrowed(&self.min.0), &self.min.1));
            }
            (Ordering::Equal, Some((summary, children))) => {
                let (hi, ()) = summary.max_val();
                let child = children.get(&hi).unwrap();
                let (lo, val) = child.max_val();
                return Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val));
            }
            (Ordering::Less, Some((summary, children))) => (summary, children),
        };

        K::split_ref(&*k, |hi, lo| {
            // Try to find the child where `k` is expected to live (identified by `hi`)
            // Then ask that node for the predecessor to `lo`. This is expected to short circuit if `lo` is outside the range of `child`
            let lo = children.get(&*hi).and_then(|child| child.predecessor(lo));
            if let Some((lo, val)) = lo {
                return Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val));
            }

            // If we didn't find it, find the predecessor to `hi` in the summary and use the `min` of that node
            if let Some((hi, ())) = summary.predecessor(hi) {
                let hi: MaybeBorrowed<K::Hi> = hi.into();
                let child = children.get(&hi).unwrap();
                let (lo, val) = child.max_val();
                return Some((MaybeBorrowed::Owned(K::join(hi, lo.into())), val));
            }

            // If there are no predecessor to `hi`, then use the max value for this node
            Some((MaybeBorrowed::Borrowed(&self.min.0), &self.min.1))
        })
    }

    /// O(lg lg K)
    fn predecessor_mut<'a, Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<K>, &mut V)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = k.into();
        if *k.borrow() <= self.min.0 {
            return None;
        }

        let data = match self.data.as_mut() {
            None => return Some((MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1)),
            Some(data) => data,
        };

        let (summary, children) = match (k.borrow().cmp(&data.max.0), data.children.as_mut()) {
            (Ordering::Greater, _) => {
                return Some((MaybeBorrowed::Borrowed(&data.max.0), &mut data.max.1))
            }
            (_, None) => {
                return Some((MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1));
            }
            (Ordering::Equal, Some((summary, children))) => {
                debug_assert!(*k.borrow() > self.min.0);

                let (hi, ()) = summary.max_val();
                let child = children.get_mut(&hi).unwrap();
                let (lo, val) = child.max_val_mut();
                return Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val));
            }
            (Ordering::Less, Some((summary, children))) => (summary, children),
        };

        K::split_ref(&*k, |hi, lo| {
            // FIXME: rust-lang/rust#43234
            // Remove this polonius hack when NLL works
            use polonius_the_crab::{polonius, WithLifetime};
            type RetRef<K, V> = dyn for<'lt> WithLifetime<
                'lt,
                T = (MaybeBorrowed<'lt, <K as VebKey>::Lo>, &'lt mut V),
            >;

            trait PoloniusExt {
                type Hi;
                type Lo;
                type V;
                /// Try to find the child where `k` is expected to live (identified by `hi`)
                /// Then ask that node for the predecessor to `lo`. This is expected to short circuit if `lo` is outside the range of `child`
                fn get_mut_predecessor_mut<'lt>(
                    &'lt mut self,
                    hi: &Self::Hi,
                    lo: &Self::Lo,
                ) -> Option<(MaybeBorrowed<'lt, Self::Lo>, &'lt mut Self::V)>;
            }
            impl<T: TreeCollection> PoloniusExt for T {
                type Hi = T::Hi;
                type Lo = <T::Tree as VebTree>::Key;
                type V = <T::Tree as VebTree>::Value;
                fn get_mut_predecessor_mut<'lt>(
                    &'lt mut self,
                    hi: &Self::Hi,
                    lo: &Self::Lo,
                ) -> Option<(MaybeBorrowed<'lt, Self::Lo>, &'lt mut Self::V)> {
                    self.get_mut(hi).and_then(|child| child.predecessor_mut(lo))
                }
            }

            let polonius = {
                polonius::<RetRef<K, V>, _, _, _>(children, move |children| {
                    // Polonius hates doing this in the lambda
                    // children.get_mut(hi).and_then(|child| child.successor_mut(lo)).ok_or(())
                    // but is perfectly fine with calling it blindly through a trait extension
                    children.get_mut_predecessor_mut(hi, lo).ok_or(())
                })
            };

            let children = match polonius {
                Ok((lo, val)) => {
                    return Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val))
                }
                Err((children, ())) => children,
            };

            // If we didn't find it, find the predecessor to `hi` in the summary and use the `min` of that node
            if let Some((hi, ())) = summary.predecessor(hi) {
                let hi: MaybeBorrowed<K::Hi> = hi.into();
                let child = children.get_mut(&hi).unwrap();
                let (lo, val) = child.max_val_mut();
                return Some((MaybeBorrowed::Owned(K::join(hi, lo.into())), val));
            }

            // If there are no predecessor to `hi`, then use the max value for this node
            Some((MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1))
        })
    }

    /// O(lg lg K)
    fn successor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<K>, &V)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = k.into();
        if *k.borrow() < self.min.0 {
            return Some((MaybeBorrowed::Borrowed(&self.min.0), &self.min.1));
        }
        let data = match self.data.as_ref() {
            // k >= min, and we don't have a successor
            None => return None,
            Some(data) => data,
        };
        if *k.borrow() >= data.max.0 {
            return None;
        }
        let (summary, children) = match data.children.as_ref() {
            None => return Some((MaybeBorrowed::Borrowed(&data.max.0), &data.max.1)),
            Some((summary, children)) => (summary, children),
        };
        if *k.borrow() == self.min.0 {
            let (hi, ()) = summary.min_val();
            let child = children.get(&hi).unwrap();
            let (lo, val) = child.min_val();
            return Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val));
        }

        K::split_ref(&*k, |hi, lo| {
            // Try to find the child where `k` is expected to live (identified by `hi`)
            // Then ask that node for the successor to `lo`. This is expected to short circuit if `lo` is outside the range of `child`
            let lo = children.get(hi).and_then(|child| child.successor(lo));
            if let Some((lo, val)) = lo {
                return Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val));
            }

            // If we didn't find it, find the successor to `hi` in the summary and use the `min` of that node
            if let Some((hi, ())) = summary.successor(hi) {
                let child = children.get(&hi).unwrap();
                let (lo, val) = child.min_val();
                return Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val));
            }

            // If there are no successors to `hi`, then use the max value for this node
            Some((MaybeBorrowed::Borrowed(&data.max.0), &data.max.1))
        })
    }

    /// O(lg lg K)
    fn successor_mut<'a, 'b, Q>(&'b mut self, k: Q) -> Option<(MaybeBorrowed<'b, K>, &'b mut V)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = k.into();
        if *k.borrow() < self.min.0 {
            return Some((MaybeBorrowed::Borrowed(&self.min.0), &mut self.min.1));
        }
        let data = match self.data.as_mut() {
            // k >= min, and we don't have a successor
            None => return None,
            Some(data) => data,
        };
        if *k.borrow() >= data.max.0 {
            return None;
        }
        let (summary, children) = match data.children.as_mut() {
            None => return Some((MaybeBorrowed::Borrowed(&data.max.0), &mut data.max.1)),
            Some((summary, children)) => (summary, children),
        };
        if *k.borrow() == self.min.0 {
            let (hi, ()) = summary.min_val();
            let child = children.get_mut(&hi).unwrap();
            let (lo, val) = child.min_val_mut();
            return Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val));
        }

        K::split_ref(&*k, |hi, lo| {
            // FIXME: rust-lang/rust#43234
            // Remove this polonius hack when NLL works
            use polonius_the_crab::{polonius, WithLifetime};
            type RetRef<K, V> = dyn for<'lt> WithLifetime<
                'lt,
                T = (MaybeBorrowed<'lt, <K as VebKey>::Lo>, &'lt mut V),
            >;

            trait PoloniusExt {
                type Hi;
                type Lo;
                type V;
                /// Try to find the child where `k` is expected to live (identified by `hi`)
                /// Then ask that node for the successor to `lo`. This is expected to short circuit if `lo` is outside the range of `child`
                fn get_mut_successor_mut<'lt>(
                    &'lt mut self,
                    hi: &Self::Hi,
                    lo: &Self::Lo,
                ) -> Option<(MaybeBorrowed<'lt, Self::Lo>, &'lt mut Self::V)>;
            }
            impl<T: TreeCollection> PoloniusExt for T {
                type Hi = T::Hi;
                type Lo = <T::Tree as VebTree>::Key;
                type V = <T::Tree as VebTree>::Value;
                fn get_mut_successor_mut<'lt>(
                    &'lt mut self,
                    hi: &Self::Hi,
                    lo: &Self::Lo,
                ) -> Option<(MaybeBorrowed<'lt, Self::Lo>, &'lt mut Self::V)> {
                    self.get_mut(hi).and_then(|child| child.successor_mut(lo))
                }
            }

            let polonius = {
                polonius::<RetRef<K, V>, _, _, _>(children, move |children| {
                    // Polonius hates doing this in the lambda
                    // children.get_mut(hi).and_then(|child| child.successor_mut(lo)).ok_or(())
                    // but is perfectly fine with calling it blindly through a trait extension
                    children.get_mut_successor_mut(hi, lo).ok_or(())
                })
            };
            let children = match polonius {
                Ok((lo, val)) => {
                    return Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val))
                }
                Err((children, ())) => children,
            };

            // If we didn't find it, find the successor to `hi` in the summary and use the `min` of that node
            if let Some((hi, ())) = summary.successor(hi) {
                let child = children.get_mut(&hi).unwrap();
                let (lo, val) = child.min_val_mut();
                return Some((MaybeBorrowed::Owned(K::join(hi.into(), lo.into())), val));
            }

            // If there are no successors to `hi`, then use the max value for this node
            Some((MaybeBorrowed::Borrowed(&data.max.0), &mut data.max.1))
        })
    }

    /// O(lg lg K)
    fn insert(&mut self, k: K, v: V) -> Option<(K, V)> {
        // See if `k` should take the place of `min`. If so, swap them and store the previous `min` in subtrees
        let (k, v, data) = match (k.cmp(&self.min.0), self.data.as_mut()) {
            (Ordering::Equal, _) => return Some(replace(&mut self.min, (k, v))),
            // Monad path
            (Ordering::Less, None) => {
                let max = replace(&mut self.min, (k, v));
                self.data = Some(TreeData {
                    max,
                    children: None,
                });
                return None;
            }
            (Ordering::Greater, None) => {
                let max = (k, v);
                self.data = Some(TreeData {
                    max,
                    children: None,
                });
                return None;
            }
            (Ordering::Less, Some(data)) => {
                let (k, v) = replace(&mut self.min, (k, v));
                let (k, v) = match data.max.0.cmp(&k) {
                    Ordering::Equal => return Some(replace(&mut data.max, (k, v))),
                    Ordering::Greater => replace(&mut data.max, (k, v)),
                    Ordering::Less => (k, v),
                };

                (k, v, data)
            }
            (Ordering::Greater, Some(data)) => match k.borrow().cmp(&data.max.0) {
                Ordering::Equal => return Some(replace(&mut data.max, (k, v))),
                Ordering::Greater => {
                    let (k, v) = replace(&mut data.max, (k, v));
                    (k, v, data)
                }
                Ordering::Less => (k, v, data),
            },
        };

        let (hi, lo) = k.split_val();
        if let Some((mut summary, mut children)) = data.children.take() {
            let r = match children.insert_key(hi, (lo, v)) {
                Ok(hi) => {
                    summary.insert(hi, ());
                    None
                }
                Err((_, None)) => None,
                Err((hi, Some((lo, v)))) => Some((K::join(MaybeBorrowed::Owned(hi), lo.into()), v)),
            };
            data.children = Some((summary, children));
            r
        } else {
            let children = TC::<Children, K, V>::create(&hi, VebTree::from_monad(lo, v));
            let summary = <Summary::Tree as VebTree>::from_monad(hi, ());
            data.children = Some((summary, children));
            None
        }
    }

    /// O(lg lg K)
    fn remove<'a, Q>(mut self, k: Q) -> Result<(Option<Self>, (Self::Key, Self::Value)), Self>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = k.into();
        if self.min.0 == *k.borrow() {
            return Ok(self.remove_min());
        }

        let data = match self.data.take() {
            // Monad, but `k` not found
            None => return Err(self),
            Some(data) => data,
        };

        let (summary, children) = match data.children {
            // No children found max
            None if data.max.0 == *k.borrow() => return Ok((Some(self), data.max)),

            // No children but not max
            // so revert the take
            None => {
                self.data = Some(data);
                return Err(self);
            }
            Some((summary, children)) => (summary, children),
        };

        if data.max.0 == *k.borrow() {
            // Start by looking for the largest subtree
            let (hi, ()) = summary.max_val();
            // We should always find an entry, since we're starting from the summary
            // Try to remove the largest entry from the subtree
            let (children, (lo, val)) = children.remove_key(hi.borrow(), VebTree::remove_max);
            let new_max = (K::join(hi.into(), lo.into()), val);
            // Remove the subtree entirely if it's a monad
            let children = match children {
                None => None,
                Some((children, false)) => Some((summary, children)),
                Some((children, true)) => Some((summary.remove_max().0.unwrap(), children)),
            };
            self.data = Some(TreeData {
                max: new_max,
                children,
            });
            return Ok((Some(self), data.max));
        }

        K::split_ref(&*k, |hi, lo| {
            let (children, lo) = match children.maybe_remove_key(hi, |v| v.remove(lo)) {
                Err(children) => (Some((summary, children)), None),
                Ok((None, res)) => (None, Some(res)),
                Ok((Some((children, false)), res)) => (Some((summary, children)), Some(res)),
                Ok((Some((children, true)), res)) => (
                    Some((summary.remove(hi).ok().unwrap().0.unwrap(), children)),
                    Some(res),
                ),
            };

            self.data = Some(TreeData {
                max: data.max,
                children,
            });
            if let Some((lo, val)) = lo {
                Ok((Some(self), (K::join(hi.into(), lo.into()), val)))
            } else {
                Err(self)
            }
        })
    }

    /// O(lg lg K)
    fn remove_min(mut self) -> (Option<Self>, (K, V)) {
        let data = match self.data.take() {
            // No data, return monad
            None => return (None, self.min),
            Some(data) => data,
        };

        let (max, summary, children) = match data.children {
            // Only max, so become monad
            None => {
                let r = replace(&mut self.min, data.max);
                return (Some(self), r);
            }
            // Subtree, so extract a new `min` from the subtree
            Some((summary, children)) => (data.max, summary, children),
        };

        // Start by looking for the smallest subtree
        let (hi, ()) = summary.min_val();
        // We should always find an entry, since we're starting from the summary
        // Try to remove the smallest entry from the subtree
        let (children, (lo, val)) = children.remove_key(hi.borrow(), VebTree::remove_min);
        // Remove the subtree entirely if it's a monad
        let min = K::join(hi.into(), lo.into());
        let children = match children {
            None => None,
            Some((children, false)) => Some((summary, children)),
            Some((children, true)) => Some((summary.remove_min().0.unwrap(), children)),
        };
        self.data = Some(TreeData { max, children });
        let r = replace(&mut self.min, (min, val));
        (Some(self), r)
    }

    /// O(lg lg K)
    fn remove_max(mut self) -> (Option<Self>, (K, V)) {
        let data = match self.data.take() {
            // No data, return monad
            None => return (None, self.min),
            Some(data) => data,
        };

        let (max, summary, children) = match data.children {
            // Only max, so become monad
            None => return (Some(self), data.max),
            // Subtree, so extract a new `min` from the subtree
            Some((summary, children)) => (data.max, summary, children),
        };

        // Start by looking for the largest subtree
        let (hi, ()) = summary.max_val();
        // We should always find an entry, since we're starting from the summary
        // Try to remove the smallest entry from the subtree
        let (children, (lo, val)) = children.remove_key(hi.borrow(), VebTree::remove_max);
        let new_max = (K::join(hi.into(), lo.into()), val);
        // Remove the subtree entirely if it's a monad
        let children = match children {
            None => None,
            Some((children, false)) => Some((summary, children)),
            Some((children, true)) => Some((summary.remove_max().0.unwrap(), children)),
        };
        self.data = Some(TreeData {
            max: new_max,
            children,
        });
        (Some(self), max)
    }
}

#[cfg(test)]
mod test {
    use core::fmt;

    use crate::{
        key::MaybeBorrowed,
        markers::{Marker16, Marker32, VebTreeType},
        VebTree,
    };

    fn verify<K, V, T>(
        veb: &mut T,
        finds: impl IntoIterator<Item = (K, Option<(K, V)>)>,
        predecessors: impl IntoIterator<Item = (K, Option<(K, V)>)>,
        successors: impl IntoIterator<Item = (K, Option<(K, V)>)>,
    ) where
        K: fmt::Debug + Clone + PartialEq,
        V: fmt::Debug + PartialEq,
        T: VebTree<Key = K, Value = V>,
    {
        for (i, mut r) in finds {
            assert_eq!(
                veb.find(i.clone()),
                r.as_ref().map(|(k, v)| (MaybeBorrowed::Borrowed(k), v)),
                "find {i:?}"
            );
            assert_eq!(
                veb.find_mut(i.clone()),
                r.as_mut().map(|(k, v)| (MaybeBorrowed::Borrowed(k), v)),
                "find_mut {i:?}"
            );
        }
        for (i, mut r) in predecessors {
            assert_eq!(
                veb.predecessor(i.clone()),
                r.as_ref().map(|(k, v)| (MaybeBorrowed::Borrowed(k), v)),
                "predecessor {i:?}"
            );
            assert_eq!(
                veb.predecessor_mut(i.clone()),
                r.as_mut().map(|(k, v)| (MaybeBorrowed::Borrowed(k), v)),
                "predecessor_mut {i:?}"
            );
        }
        for (i, mut r) in successors {
            assert_eq!(
                veb.successor(i.clone()),
                r.as_ref().map(|(k, v)| (MaybeBorrowed::Borrowed(k), v)),
                "successor {i:?}"
            );
            assert_eq!(
                veb.successor_mut(i.clone()),
                r.as_mut().map(|(k, v)| (MaybeBorrowed::Borrowed(k), v)),
                "successor_mut {i:?}"
            );
        }
    }

    #[test]
    fn simple2() {
        type I32Tree = VebTreeType<i32, (f64, f64), Marker32>;
        let mut v = I32Tree::from_monad(10, (2., 5.));
        assert_eq!(v.min_val(), (MaybeBorrowed::Owned(10), &(2., 5.)));
        assert_eq!(v.max_val(), (MaybeBorrowed::Owned(10), &(2., 5.)));
        v.insert(15, (3., 1.));
        assert_eq!(v.min_val(), (MaybeBorrowed::Owned(10), &(2., 5.)));
        assert_eq!(v.max_val(), (MaybeBorrowed::Owned(15), &(3., 1.)));
    }
    #[test]
    fn simple() {
        //VebTree
        type U16Tree = VebTreeType<u16, &'static str, Marker16>;
        let mut v = U16Tree::from_monad(10, "a");

        assert_eq!(v.min_val(), (MaybeBorrowed::Owned(10), &"a"));
        assert_eq!(v.max_val(), (MaybeBorrowed::Owned(10), &"a"));
        verify::<_, _, U16Tree>(
            &mut v,
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
        assert_eq!(v.min_val(), (MaybeBorrowed::Owned(10), &"a"));
        assert_eq!(v.max_val(), (MaybeBorrowed::Owned(15), &"b"));
        verify::<_, _, U16Tree>(
            &mut v,
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
        assert_eq!(v.min_val(), (MaybeBorrowed::Owned(10), &"a"));
        assert_eq!(v.max_val(), (MaybeBorrowed::Owned(15), &"b"));
        verify::<_, _, U16Tree>(
            &mut v,
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
        let r = v.remove(14).ok().expect("remove failed");
        v = r.0.expect("remove failed");
        assert_eq!(r.1, ((14, "d")));
        verify::<_, _, U16Tree>(
            &mut v,
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

        let r = v.remove(15).ok().expect("remove failed");
        v = r.0.expect("remove failed");
        assert_eq!(r.1, ((15, "b")));
        assert_eq!(v.min_val(), (MaybeBorrowed::Owned(10), &"a"));
        assert_eq!(v.max_val(), (MaybeBorrowed::Owned(13), &"c"));
        verify::<_, _, U16Tree>(
            &mut v,
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
