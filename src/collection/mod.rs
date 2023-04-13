use core::{borrow::Borrow, marker::PhantomData};

use alloc::{boxed::Box, vec::Vec};
use ghost::phantom;

use crate::tree::VebTreeMarker;
use crate::{key::VebKey, MaybeRemoveResult};
use crate::{
    key::{MaybeBorrowed, SizedVebKey},
    RemoveResult, TreeKV, VebTree,
};

/// A marker trait to help with associated type bounds
pub trait SuperTreeCollection<K: VebKey, V> {
    type Tree: VebTree<Key = K::Lo, Value = V>;
    type TC: TreeCollection<High = K::Hi, Tree = Self::Tree>;
}

impl<K: VebKey, V, T> SuperTreeCollection<K, V> for T
where
    T: TreeCollection<High = K::Hi>,
    T::Tree: VebTree<Key = K::Lo, Value = V>,
{
    type TC = T;
    type Tree = T::Tree;
}

pub trait VebTreeCollectionMarker<K: VebKey, V> {
    type TreeCollection: SuperTreeCollection<K, V>;
}

pub type CollectionKV<TC> = TreeKV<<TC as TreeCollection>::Tree>;

pub type TreeInsertResult<'a, TC> = Result<
    MaybeBorrowed<'a, <TC as TreeCollection>::High>,
    (
        MaybeBorrowed<'a, <TC as TreeCollection>::High>,
        Option<CollectionKV<TC>>,
    ),
>;
pub type TreeRemoveResult<TC> = (Option<(TC, bool)>, CollectionKV<TC>);
pub type TreeMaybeRemoveResult<TC> = Result<TreeRemoveResult<TC>, TC>;

/// All operations are assumed to be `O(1)` complexity
pub trait TreeCollection: Sized {
    /// The key used to index this collection
    type High;
    /// The type of the trees stored in this collection
    type Tree: VebTree;

    /// Construct a collection from a single entry
    fn create(h: &Self::High, tree: Self::Tree) -> Self;

    /// Get a reference to the tree corresponding to the key `h`
    fn get(&self, h: &Self::High) -> Option<&Self::Tree>;

    /// Get a mutable reference to the tree corresponding to the key `h`
    fn get_mut(&mut self, h: &Self::High) -> Option<&mut Self::Tree>;

    /// Insert an value into a tree contained within
    ///
    /// If the collection does not contain a tree, returns `Ok` with a copy of the key
    /// to be used to recored in the summary.
    ///
    /// Otherwise insertion on the existing tree is performed and any pre-existing values
    /// are returned
    fn insert_key<'a, Q>(&'a mut self, h: Q, lv: CollectionKV<Self>) -> TreeInsertResult<'a, Self>
    where
        Q: Into<MaybeBorrowed<'a, Self::High>>,
        Self::High: 'a;

    /// Remove a value from a tree contained within.
    ///
    /// If the tree containing the value is a monad, it will be removed from
    /// the collection. If there are no remaning trees the entire collection
    /// is erased.
    fn remove_key<'a, Q, R>(self, h: Q, r: R) -> TreeRemoveResult<Self>
    where
        Q: Borrow<Self::High>,
        R: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>;

    /// Remove a value from a tree contained within.
    ///
    /// If the tree containing the value is a monad, it will be removed from
    /// the collection. If there are no remaning trees the entire collection
    /// is erased.
    fn maybe_remove_key<'a, Q, R>(self, h: Q, r: R) -> TreeMaybeRemoveResult<Self>
    where
        Q: Borrow<Self::High>,
        R: FnOnce(Self::Tree) -> MaybeRemoveResult<Self::Tree>;
}

impl<T: ?Sized + TreeCollection> TreeCollection for Box<T> {
    type High = T::High;
    type Tree = T::Tree;

    fn create(h: &Self::High, tree: Self::Tree) -> Self {
        Box::new(T::create(h, tree))
    }

    fn get(&self, h: &Self::High) -> Option<&Self::Tree> {
        (**self).get(h)
    }

    fn get_mut(&mut self, h: &Self::High) -> Option<&mut Self::Tree> {
        (**self).get_mut(h)
    }

    fn insert_key<'a, Q>(&'a mut self, h: Q, lv: CollectionKV<Self>) -> TreeInsertResult<'a, Self>
    where
        Q: Into<MaybeBorrowed<'a, Self::High>>,
        Self::High: 'a,
    {
        (**self).insert_key(h, lv)
    }

    /// Remove a value from a tree contained within.
    ///
    /// If the tree containing the value is a monad, it will be removed from
    /// the collection. If there are no remaning trees the entire collection
    /// is erased.
    fn remove_key<'a, Q, R>(self, h: Q, r: R) -> TreeRemoveResult<Self>
    where
        Q: Borrow<Self::High>,
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
        Q: Borrow<Self::High>,
        R: FnOnce(Self::Tree) -> MaybeRemoveResult<Self::Tree>,
    {
        let (t, v) = (*self).maybe_remove_key(h, r).map_err(Box::new)?;
        Ok((t.map(|(t, b)| (Box::new(t), b)), v))
    }
}

#[phantom]
pub struct ArrayTreeCollectionMarker<#[invariant] Tree = ()>;

impl<K, V, Tree> VebTreeCollectionMarker<K, V> for ArrayTreeCollectionMarker<Tree>
where
    K: VebKey,
    K::Hi: SizedVebKey,
    Tree: VebTreeMarker<K::Lo, V>,
{
    type TreeCollection = ArrayTreeCollection<K::Hi, Tree::Tree>;
}

pub struct ArrayTreeCollection<H, V> {
    array: Box<[Option<V>]>,
    count: usize,
    _marker: PhantomData<H>,
}

impl<High, V> TreeCollection for ArrayTreeCollection<High, V>
where
    High: SizedVebKey,
    V: VebTree,
{
    type High = High;
    type Tree = V;

    fn create(h: &Self::High, tree: Self::Tree) -> Self {
        let mut array = Vec::new();
        array.resize_with(High::CARDINALITY+1, || None);
        array[h.index()] = Some(tree);
        Self {
            array: array.into_boxed_slice(),
            count: 1,
            _marker: PhantomData,
        }
    }

    fn get(&self, h: &Self::High) -> Option<&Self::Tree> {
        self.array[h.index()].as_ref()
    }

    fn get_mut(&mut self, h: &Self::High) -> Option<&mut Self::Tree> {
        self.array[h.index()].as_mut()
    }

    fn insert_key<'a, Q>(&mut self, h: Q, (l, v): CollectionKV<Self>) -> TreeInsertResult<'a, Self>
    where
        Q: Into<MaybeBorrowed<'a, Self::High>>,
        Self::High: 'a,
    {
        let h = h.into();
        match &mut self.array[h.index()] {
            None => {
                self.array[h.index()] = Some(V::from_monad(l, v));
                self.count += 1;
                Ok(h)
            }
            Some(t) => {
                let v = t.insert(l, v);
                Err((h, v))
            }
        }
    }

    /// Remove a value from a tree contained within.
    ///
    /// If the tree containing the value is a monad, it will be removed from
    /// the collection. If there are no remaning trees the entire collection
    /// is erased.
    fn remove_key<'a, Q, R>(mut self, h: Q, r: R) -> TreeRemoveResult<Self>
    where
        Q: Borrow<Self::High>,
        R: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>,
    {
        let h = h.borrow();
        let t = self.array[h.index()].take().unwrap();
        let (t, val) = r(t);
        let removed = t.is_none();
        if removed {
            self.count -= 1;
        }
        self.array[h.index()] = t;
        if self.count == 0 {
            (None, val)
        } else {
            (Some((self, removed)), val)
        }
    }

    /// Remove a value from a tree contained within.
    ///
    /// If the tree containing the value is a monad, it will be removed from
    /// the collection. If there are no remaning trees the entire collection
    /// is erased.
    fn maybe_remove_key<'a, Q, R>(mut self, h: Q, r: R) -> TreeMaybeRemoveResult<Self>
    where
        Q: Borrow<Self::High>,
        R: FnOnce(Self::Tree) -> MaybeRemoveResult<Self::Tree>,
    {
        let h = h.borrow();
        let t = match self.array[h.index()].take() {
            None => return Err(self),
            Some(t) => t,
        };
        match r(t) {
            Err(t) => {
                self.array[h.index()] = Some(t);
                Err(self)
            }
            Ok((t, val)) => {
                let removed = t.is_none();
                if removed {
                    self.count -= 1;
                }
                self.array[h.index()] = t;
                Ok(if self.count == 0 {
                    (None, val)
                } else {
                    (Some((self, removed)), val)
                })
            }
        }
    }
}
