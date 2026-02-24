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
    K::Cardinality: ArrayLength,
{
    type Array = GenericArray<Option<Tree::Tree>, K::Cardinality>;
}

impl<V: VebTree, Cardinality: ArrayLength> OptionArray<Cardinality>
    for GenericArray<Option<V>, Cardinality>
{
    type V = V;
    fn create() -> Self {
        Self::default()
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
        // SAFETY: array is expected to contain a tree at the key's index
        let t = self
            .array
            .get_mut(h.index())
            .take()
            .expect("array should contain tree at key index");
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::{bitset::ByteSet, VebTree};
    use alloc::boxed::Box;

    type TestArray = ArrayTreeCollection<u8, Box<[Option<ByteSet>]>>;

    #[test]
    fn array_collection_create() {
        let tree = ByteSet::from_monad(5, ());
        let collection = TestArray::create(&10, tree);

        assert_eq!(collection.count, 1);
        assert!(collection.get(&10).is_some());
        assert!(collection.get(&11).is_none());
    }

    #[test]
    fn array_collection_get_operations() {
        let tree = ByteSet::from_monad(5, ());
        let mut collection = TestArray::create(&10, tree);

        // Get existing key
        assert!(collection.get(&10).is_some());
        assert!(collection.get_mut(&10).is_some());

        // Get non-existing key
        assert!(collection.get(&20).is_none());
        assert!(collection.get_mut(&20).is_none());

        // Verify correct tree is returned
        let retrieved = collection.get(&10).unwrap();
        assert!(retrieved.is_present(5));
    }

    #[test]
    fn array_collection_insert_new_key() {
        let tree1 = ByteSet::from_monad(5, ());
        let mut collection = TestArray::create(&10, tree1);

        // Insert at new index
        let result = collection.insert_key(20, (7, ()));
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 20);
        assert_eq!(collection.count, 2);

        // Verify both trees exist
        assert!(collection.get(&10).is_some());
        assert!(collection.get(&20).is_some());
    }

    #[test]
    fn array_collection_insert_existing_key() {
        let tree = ByteSet::from_monad(5, ());
        let mut collection = TestArray::create(&10, tree);

        // Insert into existing tree
        let result = collection.insert_key(10, (7, ()));
        assert!(result.is_err());
        let (key, val) = result.unwrap_err();
        assert_eq!(key, 10);
        assert!(val.is_none()); // New element added to tree
        assert_eq!(collection.count, 1); // Count unchanged
    }

    #[test]
    fn array_collection_remove_last_element_in_tree() {
        let tree = ByteSet::from_monad(5, ());
        let collection = TestArray::create(&10, tree);

        // Remove only element from tree
        let (result, (key, _val)) = collection.remove_key(&10, |t| t.remove(5).unwrap());
        assert!(result.is_none()); // Collection should be empty
        assert_eq!(key, 5);
    }

    #[test]
    fn array_collection_remove_one_element_from_tree() {
        let mut tree = ByteSet::from_monad(5, ());
        tree.insert(6, ());
        let collection = TestArray::create(&10, tree);

        // Remove one element, tree still has elements
        let (result, (key, _val)) = collection.remove_key(&10, |t| t.remove(5).unwrap());
        let (collection, removed) = result.unwrap();
        assert_eq!(collection.count, 1); // Still 1 tree
        assert!(!removed); // Tree not removed
        assert_eq!(key, 5);

        // Verify remaining element
        let remaining_tree = collection.get(&10).unwrap();
        assert!(remaining_tree.is_present(6));
        assert!(!remaining_tree.is_present(5));
    }

    #[test]
    fn array_collection_remove_entire_tree() {
        let mut tree1 = ByteSet::from_monad(5, ());
        tree1.insert(6, ());
        let mut collection = TestArray::create(&10, tree1);

        collection.insert_key(20, (7, ())).unwrap();
        assert_eq!(collection.count, 2);

        // Remove all elements from first tree
        let (result, _) = collection.remove_key(&10, |t| t.remove(5).unwrap());
        let (collection, removed) = result.unwrap();
        assert!(!removed); // First removal didn't remove tree

        let (result, _) = collection.remove_key(&10, |t| t.remove(6).unwrap());
        let (collection, removed) = result.unwrap();
        assert!(removed); // Second removal removed the tree
        assert_eq!(collection.count, 1); // Only one tree left
        assert!(collection.get(&10).is_none());
        assert!(collection.get(&20).is_some());
    }

    #[test]
    fn array_collection_maybe_remove_not_found() {
        let tree = ByteSet::from_monad(5, ());
        let collection = TestArray::create(&10, tree);

        // Try to remove from non-existing key (array slot is None)
        let result = collection.maybe_remove_key(&20, |t| t.remove(5));
        assert!(result.is_err());
    }

    #[test]
    fn array_collection_maybe_remove_element_not_in_tree() {
        let tree = ByteSet::from_monad(5, ());
        let collection = TestArray::create(&10, tree);

        // Try to remove element that doesn't exist in tree
        let result = collection.maybe_remove_key(&10, |t| t.remove(99));
        assert!(result.is_err());
    }

    #[test]
    fn array_collection_maybe_remove_success() {
        let tree = ByteSet::from_monad(5, ());
        let collection = TestArray::create(&10, tree);

        let result = collection.maybe_remove_key(&10, |t| t.remove(5));
        assert!(result.is_ok());
        let (coll, (key, _val)) = result.ok().unwrap();
        assert!(coll.is_none()); // Collection empty
        assert_eq!(key, 5);
    }

    #[test]
    fn array_collection_boundary_keys() {
        // Test with min and max u8 values
        let tree_min = ByteSet::from_monad(0, ());
        let mut collection = TestArray::create(&0u8, tree_min);

        collection.insert_key(255u8, (255, ())).unwrap();

        assert!(collection.get(&0).is_some());
        assert!(collection.get(&255).is_some());
        assert_eq!(collection.count, 2);
    }

    #[test]
    fn array_collection_all_slots_filled() {
        // Create collection and fill multiple slots
        let tree = ByteSet::from_monad(0, ());
        let mut collection = TestArray::create(&0u8, tree);

        // Add trees at various indices
        for key in [1u8, 50, 100, 150, 200, 255] {
            collection.insert_key(key, (key, ())).unwrap();
        }

        assert_eq!(collection.count, 7); // 0 + 6 more
        for key in [0u8, 1, 50, 100, 150, 200, 255] {
            assert!(collection.get(&key).is_some());
        }
    }
}
