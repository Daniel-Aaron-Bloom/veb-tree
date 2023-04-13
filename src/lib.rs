#![no_std]

extern crate alloc;

pub mod bitset;
pub mod collection;
pub mod hash;
pub mod key;
pub mod tree;

use alloc::boxed::Box;
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
    fn min_val(&self) -> (MaybeBorrowed<Self::Key>, &Self::Value);

    /// Returns the minimum value stored in the tree
    ///
    /// Complexity is expected to be `O(1)`.
    fn min_val_mut(&mut self) -> (MaybeBorrowed<Self::Key>, &mut Self::Value);

    /// Returns the maximum value stored in the tree
    ///
    /// Complexity is expected to be `O(1)`.
    fn max_val(&self) -> (MaybeBorrowed<Self::Key>, &Self::Value);

    /// Returns the maximum value stored in the tree
    ///
    /// Complexity is expected to be `O(1)`.
    fn max_val_mut(&mut self) -> (MaybeBorrowed<Self::Key>, &mut Self::Value);

    /// Gets the given key’s corresponding entry in the tree.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    // fn entry<Q>(&self, k: Q) -> Entry<Self::Occupied<'_>, Self::Vacant<'_>>
    // where
    //     Q: Borrow<Self::Key> + Into<Owned<Self::Key>>;

    /// Find a key in the tree if present.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn find<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a;

    /// Find a key in the tree if present.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn find_mut<'a, Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn predecessor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn predecessor_mut<'a, Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn successor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn successor_mut<'a, Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a;

    /// Insert a value into the tree at key `k`. If `k` was already present,
    /// replace and return the previously stored values.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn insert(&mut self, k: Self::Key, v: Self::Value) -> Option<TreeKV<Self>>;

    /// Removes a value from the tree
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn remove<'a, Q>(self, k: Q) -> MaybeRemoveResult<Self>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a;

    /// Removes the minimum value from a tree
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn remove_min(self) -> RemoveResult<Self>;

    /// Removes the maximum value from a tree
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn remove_max(self) -> RemoveResult<Self>;
}

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

impl<'a, V: VebTree> ExactSizeIterator for Iter<'a, SizedVebTree<V>> where V::Key: Clone {}

/// A [`VebTree`] that memorizes it's size
pub struct SizedVebTree<V> {
    tree: V,
    size: usize,
}

impl<V> SizedVebTree<V> {
    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.size
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

    fn min_val(&self) -> (MaybeBorrowed<Self::Key>, &Self::Value) {
        self.tree.min_val()
    }

    fn min_val_mut(&mut self) -> (MaybeBorrowed<Self::Key>, &mut Self::Value) {
        self.tree.min_val_mut()
    }

    fn max_val(&self) -> (MaybeBorrowed<Self::Key>, &Self::Value) {
        self.tree.max_val()
    }

    fn max_val_mut(&mut self) -> (MaybeBorrowed<Self::Key>, &mut Self::Value) {
        self.tree.max_val_mut()
    }

    fn find<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        self.tree.find(k)
    }

    fn find_mut<'a, Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        self.tree.find_mut(k)
    }

    fn predecessor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        self.tree.predecessor(k)
    }

    fn predecessor_mut<'a, Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        self.tree.predecessor_mut(k)
    }

    fn successor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        self.tree.successor(k)
    }

    fn successor_mut<'a, Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
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

    fn remove<'a, Q>(mut self, k: Q) -> MaybeRemoveResult<Self>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
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

impl<V: ?Sized + VebTree> VebTree for Box<V> {
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

    fn min_val(&self) -> (MaybeBorrowed<Self::Key>, &Self::Value) {
        (**self).min_val()
    }

    fn min_val_mut(&mut self) -> (MaybeBorrowed<Self::Key>, &mut Self::Value) {
        (**self).min_val_mut()
    }

    fn max_val(&self) -> (MaybeBorrowed<Self::Key>, &Self::Value) {
        (**self).max_val()
    }

    fn max_val_mut(&mut self) -> (MaybeBorrowed<Self::Key>, &mut Self::Value) {
        (**self).max_val_mut()
    }

    fn find<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        (**self).find(k)
    }

    fn find_mut<'a, Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        (**self).find_mut(k)
    }

    fn predecessor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        (**self).predecessor(k)
    }

    fn predecessor_mut<'a, Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        (**self).predecessor_mut(k)
    }

    fn successor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        (**self).successor(k)
    }

    fn successor_mut<'a, Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        (**self).successor_mut(k)
    }

    fn insert(&mut self, k: Self::Key, v: Self::Value) -> Option<(Self::Key, Self::Value)> {
        (**self).insert(k, v)
    }

    fn remove<'a, Q>(self, k: Q) -> MaybeRemoveResult<Self>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
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
