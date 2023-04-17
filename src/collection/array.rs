use core::iter::repeat_with;
use core::{borrow::Borrow, marker::PhantomData};

use alloc::{boxed::Box, vec::Vec};
use generic_array::{ArrayLength, GenericArray};
use ghost::phantom;
use typenum::Unsigned;

use crate::markers::BoxMarker;
use crate::tree::VebTreeMarker;
use crate::{key::SizedVebKey, RemoveResult, VebTree};
use crate::{key::VebKey, MaybeRemoveResult};

use super::{
    CollectionKV, TreeCollection, TreeInsertResult, TreeMaybeRemoveResult, TreeRemoveResult,
    VebTreeCollectionMarker,
};

#[phantom]
pub struct ArrayTreeCollectionMarker<Array>;

impl<K, V, A> VebTreeCollectionMarker<K, V> for ArrayTreeCollectionMarker<A>
where
    K: VebKey,
    K::Hi: SizedVebKey,
    A: ArrayMarker<K::Hi, V>,
    <A::Array as OptionArray<<K::Hi as SizedVebKey>::Cardinality>>::V:
        VebTree<Key = K::Lo, Value = V>,
{
    type TreeCollection = ArrayTreeCollection<K::Hi, A::Array>;
}

pub trait ArrayMarker<K: SizedVebKey, V> {
    type Array: OptionArray<K::Cardinality>;
}

impl<K: SizedVebKey, V, T: VebTreeMarker<K, V>> ArrayMarker<K, V> for BoxMarker<T> {
    type Array = Box<[Option<T::Tree>]>;
}

pub trait OptionArray<Cardinality> {
    type V: VebTree;
    fn create() -> Self;
    fn get(&self, i: usize) -> &Option<Self::V>;
    fn get_mut(&mut self, i: usize) -> &mut Option<Self::V>;
}

impl<V: VebTree, Cardinality: Unsigned> OptionArray<Cardinality> for Box<[Option<V>]> {
    type V = V;
    fn create() -> Self {
        let mut array = Vec::new();
        array.resize_with(Cardinality::USIZE, || None);
        array.into_boxed_slice()
    }
    fn get(&self, i: usize) -> &Option<Self::V> {
        &self[i]
    }
    fn get_mut(&mut self, i: usize) -> &mut Option<Self::V> {
        &mut self[i]
    }
}

#[phantom]
pub struct GenericArrayMarker<T>;

impl<K: SizedVebKey, V, Tree: VebTreeMarker<K, V>> ArrayMarker<K, V> for GenericArrayMarker<Tree>
where
    K::Cardinality: ArrayLength<Option<Tree::Tree>>,
{
    type Array = GenericArray<Option<Tree::Tree>, K::Cardinality>;
}

impl<V: VebTree, Cardinality: ArrayLength<Option<V>>> OptionArray<Cardinality>
    for GenericArray<Option<V>, Cardinality>
{
    type V = V;
    fn create() -> Self {
        Self::from_exact_iter(repeat_with(|| None).take(Cardinality::USIZE)).unwrap()
    }
    fn get(&self, i: usize) -> &Option<Self::V> {
        &self[i]
    }
    fn get_mut(&mut self, i: usize) -> &mut Option<Self::V> {
        &mut self[i]
    }
}

pub struct ArrayTreeCollection<H, A> {
    array: A,
    count: usize,
    _marker: PhantomData<H>,
}

impl<Hi, A> TreeCollection for ArrayTreeCollection<Hi, A>
where
    Hi: SizedVebKey,
    A: OptionArray<Hi::Cardinality>,
{
    type Hi = Hi;
    type Tree = A::V;

    #[inline(never)]
    fn create(h: &Self::Hi, tree: Self::Tree) -> Self {
        let mut array = A::create();
        *array.get_mut(h.index()) = Some(tree);
        Self {
            array,
            count: 1,
            _marker: PhantomData,
        }
    }

    fn get(&self, h: &Self::Hi) -> Option<&Self::Tree> {
        self.array.get(h.index()).as_ref()
    }

    fn get_mut(&mut self, h: &Self::Hi) -> Option<&mut Self::Tree> {
        self.array.get_mut(h.index()).as_mut()
    }

    fn insert_key(&mut self, h: Self::Hi, (l, v): CollectionKV<Self>) -> TreeInsertResult<Self> {
        match self.array.get_mut(h.index()) {
            None => {
                *self.array.get_mut(h.index()) = Some(A::V::from_monad(l, v));
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
        Q: Borrow<Self::Hi>,
        R: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>,
    {
        let h = h.borrow();
        let t = self.array.get_mut(h.index()).take().unwrap();
        let (t, val) = r(t);
        let removed = t.is_none();
        if removed {
            self.count -= 1;
        }
        *self.array.get_mut(h.index()) = t;
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
        Q: Borrow<Self::Hi>,
        R: FnOnce(Self::Tree) -> MaybeRemoveResult<Self::Tree>,
    {
        let h = h.borrow();
        let t = match self.array.get_mut(h.index()).take() {
            None => return Err(self),
            Some(t) => t,
        };
        match r(t) {
            Err(t) => {
                *self.array.get_mut(h.index()) = Some(t);
                Err(self)
            }
            Ok((t, val)) => {
                let removed = t.is_none();
                if removed {
                    self.count -= 1;
                }
                *self.array.get_mut(h.index()) = t;
                Ok(if self.count == 0 {
                    (None, val)
                } else {
                    (Some((self, removed)), val)
                })
            }
        }
    }
}
