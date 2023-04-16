use core::borrow::Borrow;

use alloc::boxed::Box;

use crate::{key::VebKey, MaybeRemoveResult};
use crate::{RemoveResult, TreeKV, VebTree};

pub mod array;
pub mod hash;

/// A marker trait to help with associated type bounds
pub trait SuperTreeCollection<K: VebKey, V> {
    type Tree: VebTree<Key = K::Lo, Value = V>;
    type TC: TreeCollection<Hi = K::Hi, Tree = Self::Tree>;
}

impl<K: VebKey, V, T> SuperTreeCollection<K, V> for T
where
    T: TreeCollection<Hi = K::Hi>,
    T::Tree: VebTree<Key = K::Lo, Value = V>,
{
    type TC = T;
    type Tree = T::Tree;
}

pub trait VebTreeCollectionMarker<K: VebKey, V> {
    type TreeCollection: SuperTreeCollection<K, V>;
}

pub type CollectionKV<TC> = TreeKV<<TC as TreeCollection>::Tree>;

pub type TreeInsertResult<TC> =
    Result<<TC as TreeCollection>::Hi, (<TC as TreeCollection>::Hi, Option<CollectionKV<TC>>)>;
pub type TreeRemoveResult<TC> = (Option<(TC, bool)>, CollectionKV<TC>);
pub type TreeMaybeRemoveResult<TC> = Result<TreeRemoveResult<TC>, TC>;

/// All operations are assumed to be `O(1)` complexity
pub trait TreeCollection: Sized {
    /// The key used to index this collection
    type Hi;
    /// The type of the trees stored in this collection
    type Tree: VebTree;

    /// Construct a collection from a single entry
    fn create(h: &Self::Hi, tree: Self::Tree) -> Self;

    /// Get a reference to the tree corresponding to the key `h`
    fn get(&self, h: &Self::Hi) -> Option<&Self::Tree>;

    /// Get a mutable reference to the tree corresponding to the key `h`
    fn get_mut(&mut self, h: &Self::Hi) -> Option<&mut Self::Tree>;

    /// Insert an value into a tree contained within
    ///
    /// If the collection does not contain a tree, returns `Ok` with a copy of the key
    /// to be used to recored in the summary.
    ///
    /// Otherwise insertion on the existing tree is performed and any pre-existing values
    /// are returned
    fn insert_key(&mut self, h: Self::Hi, lv: CollectionKV<Self>) -> TreeInsertResult<Self>;

    /// Remove a value from a tree contained within.
    ///
    /// If the tree containing the value is a monad, it will be removed from
    /// the collection. If there are no remaning trees the entire collection
    /// is erased.
    fn remove_key<'a, Q, R>(self, h: Q, r: R) -> TreeRemoveResult<Self>
    where
        Q: Borrow<Self::Hi>,
        R: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>;

    /// Remove a value from a tree contained within.
    ///
    /// If the tree containing the value is a monad, it will be removed from
    /// the collection. If there are no remaning trees the entire collection
    /// is erased.
    fn maybe_remove_key<'a, Q, R>(self, h: Q, r: R) -> TreeMaybeRemoveResult<Self>
    where
        Q: Borrow<Self::Hi>,
        R: FnOnce(Self::Tree) -> MaybeRemoveResult<Self::Tree>;
}

impl<T: ?Sized + TreeCollection> TreeCollection for Box<T> {
    type Hi = T::Hi;
    type Tree = T::Tree;

    fn create(h: &Self::Hi, tree: Self::Tree) -> Self {
        Box::new(T::create(h, tree))
    }

    fn get(&self, h: &Self::Hi) -> Option<&Self::Tree> {
        (**self).get(h)
    }

    fn get_mut(&mut self, h: &Self::Hi) -> Option<&mut Self::Tree> {
        (**self).get_mut(h)
    }

    fn insert_key(&mut self, h: Self::Hi, lv: CollectionKV<Self>) -> TreeInsertResult<Self> {
        (**self).insert_key(h, lv)
    }

    /// Remove a value from a tree contained within.
    ///
    /// If the tree containing the value is a monad, it will be removed from
    /// the collection. If there are no remaning trees the entire collection
    /// is erased.
    fn remove_key<'a, Q, R>(self, h: Q, r: R) -> TreeRemoveResult<Self>
    where
        Q: Borrow<Self::Hi>,
        R: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>,
    {
        let (t, v) = (*self).remove_key(h, r);
        (t.map(|(t, b)| (Box::new(t), b)), v)
    }

    /// Remove a value from a tree contained within.
    ///
    /// If the tree containing the value is a monad, it will be removed from
    /// the collection. If there are no remaning trees the entire collection
    /// is erased.
    fn maybe_remove_key<'a, Q, R>(self, h: Q, r: R) -> TreeMaybeRemoveResult<Self>
    where
        Q: Borrow<Self::Hi>,
        R: FnOnce(Self::Tree) -> MaybeRemoveResult<Self::Tree>,
    {
        let (t, v) = (*self).maybe_remove_key(h, r).map_err(Box::new)?;
        Ok((t.map(|(t, b)| (Box::new(t), b)), v))
    }
}
