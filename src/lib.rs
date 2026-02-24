#![no_std]
#![recursion_limit = "256"]

extern crate alloc;

pub mod bitset;
pub mod collection;
pub mod iter;
pub mod key;
pub mod markers;
pub mod tree;

use core::{borrow::Borrow, mem::replace, ops::Bound};

use alloc::{boxed::Box, collections::BTreeMap};
use key::MaybeBorrowed;

/// A shorthand for a kv-pair
pub type TreeKV<VT> = (<VT as VebTree>::Key, <VT as VebTree>::Value);

/// The possible results from a call to [`VebTree::remove_min`]/[`VebTree::remove_max`]
pub type RemoveResult<VT> = (Option<VT>, TreeKV<VT>);

/// The possible results from a call to [`VebTree::remove`]
pub type MaybeRemoveResult<VT> = Result<RemoveResult<VT>, VT>;

pub trait VebTree: Sized {
    /// The key used to index the [`VebTree`].
    type Key: Ord;
    /// The value stored in the [`VebTree`].
    type Value;

    /// Construct a monad tree from `key`.
    ///
    /// Complexity is expected to be `O(1)`.
    fn from_monad(key: Self::Key, val: Self::Value) -> Self;

    /// Returns `true` if the tree is a monad
    ///
    /// Complexity is expected to be `O(1)`.
    fn is_monad(&self) -> bool;

    /// Returns the bounds on the size of the tree.
    ///
    /// Complexity is expected to be `O(1)`.
    fn len_hint(&self) -> (usize, Option<usize>) {
        if self.is_monad() {
            (1, None)
        } else {
            (2, None)
        }
    }

    /// Deconstruct a monad tree into a `Key`.
    ///
    /// Complexity is expected to be `O(1)`.
    fn into_monad(self) -> Result<TreeKV<Self>, Self>;

    /// Returns the minimum value stored in the tree
    ///
    /// Complexity is expected to be `O(1)`.
    fn min_val(&self) -> (MaybeBorrowed<'_, Self::Key>, &Self::Value);

    /// Returns the minimum value stored in the tree
    ///
    /// Complexity is expected to be `O(1)`.
    fn min_val_mut(&mut self) -> (MaybeBorrowed<'_, Self::Key>, &mut Self::Value);

    /// Returns the maximum value stored in the tree
    ///
    /// Complexity is expected to be `O(1)`.
    fn max_val(&self) -> (MaybeBorrowed<'_, Self::Key>, &Self::Value);

    /// Returns the maximum value stored in the tree
    ///
    /// Complexity is expected to be `O(1)`.
    fn max_val_mut(&mut self) -> (MaybeBorrowed<'_, Self::Key>, &mut Self::Value);

    // Gets the given key’s corresponding entry in the tree.
    //
    // Complexity is expected to be `O(lg lg K)`.
    // fn entry<Q>(&self, k: Q) -> Entry<Self::Occupied<'_>, Self::Vacant<'_>>
    // where
    //     Q: Borrow<Self::Key> + Into<Owned<Self::Key>>;

    /// Find a key in the tree if present.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn find<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>;

    /// Find a key in the tree if present.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn find_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn predecessor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn predecessor_mut<Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn successor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn successor_mut<Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>;

    /// Insert a value into the tree at key `k`. If `k` was already present,
    /// replace and return the previously stored values.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn insert(&mut self, k: Self::Key, v: Self::Value) -> Option<TreeKV<Self>>;

    /// Removes a value from the tree
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn remove<Q>(self, k: Q) -> MaybeRemoveResult<Self>
    where
        Q: Borrow<Self::Key>;

    /// Removes the minimum value from a tree
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn remove_min(self) -> RemoveResult<Self>;

    /// Removes the maximum value from a tree
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn remove_max(self) -> RemoveResult<Self>;
}

// Re-export Iter from the iter module
pub use iter::Iter;

impl<'a, V: VebTree> ExactSizeIterator for Iter<'a, SizedVebTree<V>> where V::Key: Clone {}

/// A [`VebTree`] that memorizes it's size
pub struct SizedVebTree<V> {
    tree: V,
    size: usize,
}

impl<V> SizedVebTree<V> {
    /// Returns the number of elements in the map.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.size
    }
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<V: VebTree> VebTree for SizedVebTree<V> {
    type Key = V::Key;
    type Value = V::Value;

    fn from_monad(key: Self::Key, val: Self::Value) -> Self {
        SizedVebTree {
            tree: V::from_monad(key, val),
            size: 1,
        }
    }

    fn is_monad(&self) -> bool {
        if self.tree.is_monad() {
            debug_assert!(self.size == 1);
            true
        } else {
            false
        }
    }

    fn len_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }

    fn into_monad(self) -> Result<(Self::Key, Self::Value), Self> {
        self.tree.into_monad().map_err(|tree| SizedVebTree {
            tree,
            size: self.size,
        })
    }

    fn min_val(&self) -> (MaybeBorrowed<'_, Self::Key>, &Self::Value) {
        self.tree.min_val()
    }

    fn min_val_mut(&mut self) -> (MaybeBorrowed<'_, Self::Key>, &mut Self::Value) {
        self.tree.min_val_mut()
    }

    fn max_val(&self) -> (MaybeBorrowed<'_, Self::Key>, &Self::Value) {
        self.tree.max_val()
    }

    fn max_val_mut(&mut self) -> (MaybeBorrowed<'_, Self::Key>, &mut Self::Value) {
        self.tree.max_val_mut()
    }

    fn find<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        self.tree.find(k)
    }

    fn find_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        self.tree.find_mut(k)
    }

    fn predecessor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        self.tree.predecessor(k)
    }

    fn predecessor_mut<Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        self.tree.predecessor_mut(k)
    }

    fn successor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        self.tree.successor(k)
    }

    fn successor_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        self.tree.successor_mut(k)
    }

    fn insert(&mut self, k: Self::Key, v: Self::Value) -> Option<(Self::Key, Self::Value)> {
        let v = self.tree.insert(k, v);
        if v.is_none() {
            self.size += 1;
        }
        v
    }

    fn remove<Q>(mut self, k: Q) -> MaybeRemoveResult<Self>
    where
        Q: Borrow<Self::Key>,
    {
        match self.tree.remove(k) {
            Ok((Some(tree), r)) => {
                self.tree = tree;
                self.size -= 1;
                Ok((Some(self), r))
            }
            Ok((None, v)) => Ok((None, v)),
            Err(tree) => {
                self.tree = tree;
                Err(self)
            }
        }
    }

    fn remove_min(mut self) -> (Option<Self>, (Self::Key, Self::Value)) {
        self.size -= 1;
        let (tree, v) = self.tree.remove_min();
        if let Some(tree) = tree {
            self.tree = tree;
            (Some(self), v)
        } else {
            (None, v)
        }
    }

    fn remove_max(mut self) -> (Option<Self>, (Self::Key, Self::Value)) {
        self.size -= 1;
        let (tree, v) = self.tree.remove_max();
        if let Some(tree) = tree {
            self.tree = tree;
            (Some(self), v)
        } else {
            (None, v)
        }
    }
}

impl<V: VebTree> VebTree for Box<V> {
    type Key = V::Key;
    type Value = V::Value;

    fn from_monad(key: Self::Key, val: Self::Value) -> Self {
        Box::new(V::from_monad(key, val))
    }

    fn is_monad(&self) -> bool {
        (**self).is_monad()
    }

    fn len_hint(&self) -> (usize, Option<usize>) {
        (**self).len_hint()
    }

    fn into_monad(self) -> Result<(Self::Key, Self::Value), Self> {
        (*self).into_monad().map_err(Box::new)
    }

    fn min_val(&self) -> (MaybeBorrowed<'_, Self::Key>, &Self::Value) {
        (**self).min_val()
    }

    fn min_val_mut(&mut self) -> (MaybeBorrowed<'_, Self::Key>, &mut Self::Value) {
        (**self).min_val_mut()
    }

    fn max_val(&self) -> (MaybeBorrowed<'_, Self::Key>, &Self::Value) {
        (**self).max_val()
    }

    fn max_val_mut(&mut self) -> (MaybeBorrowed<'_, Self::Key>, &mut Self::Value) {
        (**self).max_val_mut()
    }

    fn find<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        (**self).find(k)
    }

    fn find_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        (**self).find_mut(k)
    }

    fn predecessor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        (**self).predecessor(k)
    }

    fn predecessor_mut<Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        (**self).predecessor_mut(k)
    }

    fn successor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        (**self).successor(k)
    }

    fn successor_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        (**self).successor_mut(k)
    }

    fn insert(&mut self, k: Self::Key, v: Self::Value) -> Option<(Self::Key, Self::Value)> {
        (**self).insert(k, v)
    }

    fn remove<Q>(self, k: Q) -> MaybeRemoveResult<Self>
    where
        Q: Borrow<Self::Key>,
    {
        match (*self).remove(k) {
            Ok((tree, r)) => Ok((tree.map(Box::new), r)),
            Err(tree) => Err(Box::new(tree)),
        }
    }

    fn remove_min(self) -> (Option<Self>, (Self::Key, Self::Value)) {
        let (tree, v) = (*self).remove_min();
        (tree.map(Box::new), v)
    }

    fn remove_max(self) -> (Option<Self>, (Self::Key, Self::Value)) {
        let (tree, v) = (*self).remove_max();
        (tree.map(Box::new), v)
    }
}

impl<K: Ord, V> VebTree for BTreeMap<K, V> {
    type Key = K;
    type Value = V;

    fn from_monad(key: Self::Key, val: Self::Value) -> Self {
        let mut t = BTreeMap::new();
        <BTreeMap<K, V>>::insert(&mut t, key, val);
        t
    }
    fn is_monad(&self) -> bool {
        self.len() == 1
    }
    fn len_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
    fn into_monad(self) -> Result<TreeKV<Self>, Self> {
        if self.is_monad() {
            // SAFETY: is_monad() guarantees self.len() == 1, so next() must return Some
            Ok(self
                .into_iter()
                .next()
                .expect("monad BTreeMap should have one element"))
        } else {
            Err(self)
        }
    }
    fn min_val(&self) -> (MaybeBorrowed<'_, Self::Key>, &Self::Value) {
        // SAFETY: VebTree invariant - all trees are non-empty
        let (k, v) = self.iter().next().expect("tree should not be empty");
        (MaybeBorrowed::Borrowed(k), v)
    }
    fn min_val_mut(&mut self) -> (MaybeBorrowed<'_, Self::Key>, &mut Self::Value) {
        // SAFETY: VebTree invariant - all trees are non-empty
        let (k, v) = self.iter_mut().next().expect("tree should not be empty");
        (MaybeBorrowed::Borrowed(k), v)
    }
    fn max_val(&self) -> (MaybeBorrowed<'_, Self::Key>, &Self::Value) {
        // SAFETY: VebTree invariant - all trees are non-empty
        let (k, v) = self.iter().next_back().expect("tree should not be empty");
        (MaybeBorrowed::Borrowed(k), v)
    }
    fn max_val_mut(&mut self) -> (MaybeBorrowed<'_, Self::Key>, &mut Self::Value) {
        // SAFETY: VebTree invariant - all trees are non-empty
        let (k, v) = self
            .iter_mut()
            .next_back()
            .expect("tree should not be empty");
        (MaybeBorrowed::Borrowed(k), v)
    }
    fn find<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        let k = k.borrow();
        <BTreeMap<K, V>>::get_key_value(self, k).map(|(k, v)| (MaybeBorrowed::Borrowed(k), v))
    }
    fn find_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        // Unfortunately there is no `get_key_value_mut` 😢
        let k = k.borrow();
        self.range_mut(k..=k)
            .next()
            .map(|(k, v)| (MaybeBorrowed::Borrowed(k), v))
    }
    fn predecessor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        let k = k.borrow();
        self.range(..k)
            .next_back()
            .map(|(k, v)| (MaybeBorrowed::Borrowed(k), v))
    }
    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn predecessor_mut<Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        let k = k.borrow();
        self.range_mut(..k)
            .next_back()
            .map(|(k, v)| (MaybeBorrowed::Borrowed(k), v))
    }
    fn successor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        let k = k.borrow();
        self.range((Bound::Excluded(k), Bound::Unbounded))
            .next()
            .map(|(k, v)| (MaybeBorrowed::Borrowed(k), v))
    }
    fn successor_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        let k = k.borrow();
        self.range_mut((Bound::Excluded(k), Bound::Unbounded))
            .next()
            .map(|(k, v)| (MaybeBorrowed::Borrowed(k), v))
    }
    fn insert(&mut self, k: Self::Key, v: Self::Value) -> Option<TreeKV<Self>> {
        // TODO: replace with `replace_entry` or whatever gets stabilized
        match BTreeMap::get_mut(self, &k) {
            None => {
                <BTreeMap<K, V>>::insert(self, k, v);
                None
            }
            Some(old) => Some((k, replace(old, v))),
        }
    }
    fn remove<Q>(mut self, k: Q) -> MaybeRemoveResult<Self>
    where
        Q: Borrow<Self::Key>,
    {
        let k = k.borrow();
        match (
            self.is_monad(),
            <BTreeMap<K, V>>::remove_entry(&mut self, k),
        ) {
            (_, None) => Err(self),
            (true, Some((k, v))) => Ok((None, (k, v))),
            (false, Some((k, v))) => Ok((Some(self), (k, v))),
        }
    }
    fn remove_min(mut self) -> RemoveResult<Self> {
        // SAFETY: VebTree invariant - all trees are non-empty
        let v = self.pop_first().expect("tree should not be empty");
        let tree = if self.is_empty() { None } else { Some(self) };

        (tree, v)
    }

    fn remove_max(mut self) -> RemoveResult<Self> {
        // SAFETY: VebTree invariant - all trees are non-empty
        let v = self.pop_last().expect("tree should not be empty");
        let tree = if self.is_empty() { None } else { Some(self) };

        (tree, v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::collections::BTreeMap;

    #[test]
    fn btreemap_basic_operations() {
        let mut tree: BTreeMap<u32, &str> = VebTree::from_monad(10, "ten");

        assert!(tree.is_monad());
        assert_eq!(tree.find(10), Some((MaybeBorrowed::Borrowed(&10), &"ten")));
        assert_eq!(tree.find(20), None);

        tree.insert(20, "twenty");
        assert!(!tree.is_monad());
        assert_eq!(
            tree.find(20),
            Some((MaybeBorrowed::Borrowed(&20), &"twenty"))
        );
    }

    #[test]
    fn btreemap_min_max() {
        let mut tree: BTreeMap<u32, i32> = VebTree::from_monad(50, 500);
        tree.insert(10, 100);
        tree.insert(90, 900);

        assert_eq!(tree.min_val(), (MaybeBorrowed::Borrowed(&10), &100));
        assert_eq!(tree.max_val(), (MaybeBorrowed::Borrowed(&90), &900));
    }

    #[test]
    fn btreemap_predecessor_successor() {
        let mut tree: BTreeMap<u32, &str> = VebTree::from_monad(10, "a");
        tree.insert(20, "b");
        tree.insert(30, "c");

        assert_eq!(
            tree.predecessor(25),
            Some((MaybeBorrowed::Borrowed(&20), &"b"))
        );
        assert_eq!(
            tree.successor(15),
            Some((MaybeBorrowed::Borrowed(&20), &"b"))
        );
        assert_eq!(tree.predecessor(10), None);
        assert_eq!(tree.successor(30), None);
    }

    #[test]
    fn btreemap_remove_operations() {
        let mut tree: BTreeMap<u32, i32> = VebTree::from_monad(10, 100);
        tree.insert(20, 200);
        tree.insert(30, 300);

        // Remove middle element
        let (remaining, (k, v)) = tree.remove(20).ok().unwrap();
        assert_eq!((k, v), (20, 200));
        let tree = remaining.unwrap();

        // Remove min
        let (remaining, (k, v)) = tree.remove_min();
        assert_eq!((k, v), (10, 100));
        let tree = remaining.unwrap();

        // Remove last element
        let (remaining, (k, v)) = tree.remove_max();
        assert_eq!((k, v), (30, 300));
        assert!(remaining.is_none());
    }

    #[test]
    fn btreemap_insert_replace() {
        let mut tree: BTreeMap<u32, &str> = VebTree::from_monad(10, "old");
        let replaced = tree.insert(10, "new");
        // BTreeMap's VebTree::insert returns the key and old value
        assert_eq!(replaced, Some("old"));
        assert_eq!(tree.find(10), Some((MaybeBorrowed::Borrowed(&10), &"new")));
    }

    #[test]
    fn btreemap_into_monad() {
        let tree: BTreeMap<u32, i32> = VebTree::from_monad(42, 100);
        let result = tree.into_monad();
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), (42, 100));
    }

    #[test]
    fn sized_vebtree_len_tracking() {
        use crate::markers::{Marker16, VebTreeType};
        type U16Tree = VebTreeType<u16, i32, Marker16>;

        let mut tree = SizedVebTree {
            tree: U16Tree::from_monad(10, 100),
            size: 1,
        };

        assert_eq!(tree.len(), 1);
        assert_eq!(tree.len_hint(), (1, Some(1)));

        tree.insert(20, 200);
        assert_eq!(tree.len(), 2);

        tree.insert(30, 300);
        assert_eq!(tree.len(), 3);

        // Replace existing
        tree.insert(20, 250);
        assert_eq!(tree.len(), 3); // Size unchanged

        // Remove
        let (remaining, _) = tree.remove(20).ok().unwrap();
        let tree = remaining.unwrap();
        assert_eq!(tree.len(), 2);
    }

    #[test]
    fn sized_vebtree_remove_all() {
        use crate::markers::{Marker16, VebTreeType};
        type U16Tree = VebTreeType<u16, i32, Marker16>;

        let mut tree = SizedVebTree {
            tree: U16Tree::from_monad(10, 100),
            size: 1,
        };
        tree.insert(20, 200);

        let (tree, _) = tree.remove_min();
        let tree = tree.unwrap();
        assert_eq!(tree.len(), 1);

        let (tree, _) = tree.remove_max();
        assert!(tree.is_none());
    }

    #[test]
    fn box_vebtree_operations() {
        use crate::markers::{Marker16, VebTreeType};
        type U16Tree = VebTreeType<u16, &'static str, Marker16>;

        let mut tree: Box<U16Tree> = Box::new(VebTree::from_monad(10, "a"));

        assert!(tree.is_monad());
        tree.insert(20, "b");
        assert!(!tree.is_monad());

        assert_eq!(tree.min_val().0, MaybeBorrowed::Owned(10));
        assert_eq!(tree.max_val().0, MaybeBorrowed::Owned(20));

        let (remaining, (k, v)) = (*tree).remove(10).ok().expect("remove failed");
        assert_eq!((k, v), (10, "a"));
        assert!(remaining.is_some());
    }
}
