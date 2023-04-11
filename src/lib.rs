#![no_std]

use core::borrow::Borrow;

pub mod bitset;
pub mod collection;
pub mod hash;
pub mod key;
pub mod tree;

use key::Owned;

/// The possible results from a call to [`VebTree::remove`]
type RemoveResult<VT> = Result<(Option<VT>, (<VT as VebTree>::Key, <VT as VebTree>::Value)), VT>;

pub trait VebTree: Sized {
    /// The key used to index the [`VebTree`].
    type Key: Ord;
    /// The value stored in the [`VebTree`].
    type Value;
    /// The key return type of [`VebTree::min_val`].
    type MinKey<'a>: Borrow<Self::Key> + Into<Owned<Self::Key>> + Into<Self::EntryKey<'a>>
    where
        (Self, Self::Key): 'a;
    /// The key return type of [`VebTree::max_val`].
    type MaxKey<'a>: Borrow<Self::Key> + Into<Owned<Self::Key>> + Into<Self::EntryKey<'a>>
    where
        (Self, Self::Key): 'a;
    /// The key return type for other methods.
    type EntryKey<'a>: Clone + Borrow<Self::Key> + Into<Owned<Self::Key>>
    where
        (Self, Self::Key): 'a;

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
    fn into_monad(self) -> Result<(Self::Key, Self::Value), Self>;

    /// Returns the minimum value stored in the tree
    ///
    /// Complexity is expected to be `O(1)`.
    fn min_val(&self) -> (Self::MinKey<'_>, &Self::Value);

    /// Returns the minimum value stored in the tree
    ///
    /// Complexity is expected to be `O(1)`.
    fn min_val_mut(&mut self) -> (Self::MinKey<'_>, &mut Self::Value);

    /// Returns the maximum value stored in the tree
    ///
    /// Complexity is expected to be `O(1)`.
    fn max_val(&self) -> (Self::MaxKey<'_>, &Self::Value);

    /// Returns the maximum value stored in the tree
    ///
    /// Complexity is expected to be `O(1)`.
    fn max_val_mut(&mut self) -> (Self::MaxKey<'_>, &mut Self::Value);

    /// Gets the given key’s corresponding entry in the tree.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    // fn entry<Q>(&self, k: Q) -> Entry<Self::Occupied<'_>, Self::Vacant<'_>>
    // where
    //     Q: Borrow<Self::Key> + Into<Owned<Self::Key>>;

    /// Find a key in the tree if present.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn find<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>;

    /// Find a key in the tree if present.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn find_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn predecessor<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn predecessor_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn successor<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>;

    /// Find the predecessor to a key, if the tree contains such a value.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn successor_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>;

    /// Insert a value into the tree at key `k`. If `k` was already present,
    /// replace and return the previously stored values.
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn insert<Q>(&mut self, k: Q, v: Self::Value) -> Option<(Self::Key, Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>;

    /// Removes a value from the tree
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn remove<Q>(self, k: Q) -> RemoveResult<Self>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>;

    /// Removes the minimum value from a tree
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn remove_min(self) -> (Option<Self>, (Self::Key, Self::Value));

    /// Removes the maximum value from a tree
    ///
    /// Complexity is expected to be `O(lg lg K)`.
    fn remove_max(self) -> (Option<Self>, (Self::Key, Self::Value));
}

/// An iterator over the key-value pairs of a [`VebTree`]
pub struct Iter<'a, V: VebTree> {
    data: Option<IterData<'a, V>>,
    emitted: usize,
}

enum IterData<'a, V: VebTree> {
    Start(&'a V),
    Front {
        prev_key: V::EntryKey<'a>,
        tree: &'a V,
    },
    Back {
        prev_key: V::EntryKey<'a>,
        tree: &'a V,
    },
    Both {
        front_key: V::EntryKey<'a>,
        back_key: V::EntryKey<'a>,
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

impl<'a, V: VebTree> Iterator for Iter<'a, V> {
    type Item = (V::EntryKey<'a>, &'a V::Value);
    fn next(&mut self) -> Option<Self::Item> {
        use IterData::*;
        let v = match self.data.take()? {
            Start(tree) => {
                let (prev_key, val) = tree.min_val();
                let prev_key: V::EntryKey<'a> = prev_key.into();
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
                let front_key: V::EntryKey<'a> = front_key.into();
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

impl<'a, V: VebTree> DoubleEndedIterator for Iter<'a, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        use IterData::*;
        let v = match self.data.take()? {
            Start(tree) => {
                let (prev_key, val) = tree.max_val();
                let prev_key: V::EntryKey<'a> = prev_key.into();
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
                let back_key: V::EntryKey<'a> = back_key.into();
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

impl<'a, V: VebTree> ExactSizeIterator for Iter<'a, SizedVebTree<V>> {}

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
    type MinKey<'a> = V::MinKey<'a>
    where
        V: 'a;
    type MaxKey<'a> = V::MaxKey<'a>
    where
        V: 'a;
    type EntryKey<'a> = V::EntryKey<'a>
    where
        V: 'a;

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

    fn min_val(&self) -> (Self::MinKey<'_>, &Self::Value) {
        self.tree.min_val()
    }

    fn min_val_mut(&mut self) -> (Self::MinKey<'_>, &mut Self::Value) {
        self.tree.min_val_mut()
    }

    fn max_val(&self) -> (Self::MaxKey<'_>, &Self::Value) {
        self.tree.max_val()
    }

    fn max_val_mut(&mut self) -> (Self::MaxKey<'_>, &mut Self::Value) {
        self.tree.max_val_mut()
    }

    fn find<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.tree.find(k)
    }

    fn find_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.tree.find_mut(k)
    }

    fn predecessor<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.tree.predecessor(k)
    }

    fn predecessor_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.tree.predecessor_mut(k)
    }

    fn successor<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.tree.successor(k)
    }

    fn successor_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.tree.successor_mut(k)
    }

    fn insert<Q>(&mut self, k: Q, v: Self::Value) -> Option<(Self::Key, Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let v = self.tree.insert(k, v);
        if v.is_none() {
            self.size += 1;
        }
        v
    }

    fn remove<Q>(mut self, k: Q) -> RemoveResult<Self>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
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
