use core::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
};

use hashbrown::{
    hash_map::{RawOccupiedEntryMut, RawVacantEntryMut},
    HashMap,
};

use crate::key::VebKey;
use crate::{key::Owned, VebTree};

/// A view into a single entry in a collection
pub enum Entry<O, V> {
    Occupied(O),
    Vacant(V),
}

impl<O, V> Entry<O, V> {
    pub fn occupied(self) -> Result<O, V> {
        match self {
            Self::Occupied(o) => Ok(o),
            Self::Vacant(v) => Err(v),
        }
    }

    pub fn vacant(self) -> Result<V, O> {
        match self {
            Self::Occupied(o) => Err(o),
            Self::Vacant(v) => Ok(v),
        }
    }
}

/// A marker trait to help with associated type bounds
pub trait SuperTreeCollection<K: VebKey, V> {
    type Tree: VebTree<Key = K::Low, Value = V>;
    type TC: TreeCollection<High = K::High, Tree = Self::Tree>;
}

impl<K: VebKey, V, T> SuperTreeCollection<K, V> for T
where
    T: TreeCollection<High = K::High>,
    T::Tree: VebTree<Key = K::Low, Value = V>,
{
    type TC = T;
    type Tree = T::Tree;
}

pub trait VebTreeCollectionMarker<K: VebKey, V> {
    type TreeCollection: SuperTreeCollection<K, V>;
}

/// All operations are assumed to be `O(1)` complexity
pub trait TreeCollection {
    /// The key used to index this collection
    type High;
    /// The type of the trees stored in this collection
    type Tree: VebTree;

    /// The GAL marker for the [`Entry::Vacant`] type
    type Vacant<'a, Q>
    where
        Self: 'a;

    /// The GAL marker for the [`Entry::Occupied`] type
    type Occupied<'a, Q>
    where
        Self: 'a;

    /// Dereference an occupied entry
    fn deref<'a, 'b, Q>(
        v: &'a mut Self::Occupied<'b, Q>,
    ) -> (&'a mut Self::High, &'a mut Self::Tree);

    /// Decompose an occupied entry
    fn decompose<'a, Q>(v: Self::Occupied<'a, Q>) -> (Q, &'a mut Self::Tree);

    /// Borrow the key from a vacant entry
    fn key<'a, 'b, Q>(v: &'a Self::Vacant<'b, Q>) -> &'a Self::High
    where
        Q: Borrow<Self::High>;

    /// Add a tree to a vacant entry
    fn insert<'a, Q>(v: Self::Vacant<'a, Q>, tree: Self::Tree) -> &'a mut Self::Tree
    where
        Q: Borrow<Self::High> + Into<Owned<Self::High>>;

    /// Remove the tree from an occupied entry
    fn remove<'a, Q>(o: Self::Occupied<'a, Q>) -> (Q, Self::High, Self::Tree);

    /// Construct a collection from a single entry
    fn create(h: &Self::High, tree: Self::Tree) -> Self;

    /// Get a reference to the tree corresponding to the key `h`
    fn get(&self, h: &Self::High) -> Option<&Self::Tree>;

    /// Get a mutable reference to the tree corresponding to the key `h`
    fn get_mut(&mut self, h: &Self::High) -> Option<&mut Self::Tree> {
        Some(Self::decompose(self.entry(h).occupied().ok()?).1)
    }

    /// Find entry for the `h` subtree
    fn entry<Q>(&mut self, h: Q) -> Entry<Self::Occupied<'_, Q>, Self::Vacant<'_, Q>>
    where
        Q: Borrow<Self::High>;
}

pub struct EntryWrapper<E, Q> {
    entry: E,
    key: Q,
}

impl<High, V, S> TreeCollection for HashMap<High, V, S>
where
    High: 'static + Clone + Eq + Hash,
    V: 'static + VebTree,
    S: 'static + BuildHasher + Default,
{
    type High = High;
    type Tree = V;

    type Vacant<'a, Q> = EntryWrapper<RawVacantEntryMut<'a, High, V, S>, Q>;
    type Occupied<'a, Q> = EntryWrapper<RawOccupiedEntryMut<'a, High, V, S>, Q>;

    fn deref<'a, 'b, Q>(
        v: &'a mut Self::Occupied<'b, Q>,
    ) -> (&'a mut Self::High, &'a mut Self::Tree) {
        v.entry.get_key_value_mut()
    }

    fn decompose<'a, Q>(v: Self::Occupied<'a, Q>) -> (Q, &'a mut Self::Tree) {
        (v.key, v.entry.into_mut())
    }

    fn key<'a, 'b, Q: Borrow<Self::High>>(v: &'a Self::Vacant<'b, Q>) -> &'a Self::High {
        v.key.borrow()
    }

    fn insert<'a, Q: Borrow<Self::High> + Into<Owned<Self::High>>>(
        v: Self::Vacant<'a, Q>,
        tree: Self::Tree,
    ) -> &'a mut Self::Tree {
        v.entry.insert(v.key.into().0, tree).1
    }

    fn remove<'a, Q>(o: Self::Occupied<'a, Q>) -> (Q, Self::High, Self::Tree) {
        let (k, v) = o.entry.remove_entry();
        (o.key, k, v)
    }

    fn create(h: &Self::High, tree: Self::Tree) -> Self {
        let v = HashMap::from_iter([(h.clone(), tree)]);
        debug_assert_eq!(v.len(), 1);
        debug_assert!(v.contains_key(h));
        v
    }

    fn get(&self, h: &Self::High) -> Option<&Self::Tree> {
        self.get(h)
    }

    fn entry<Q: Borrow<Self::High>>(
        &mut self,
        key: Q,
    ) -> Entry<Self::Occupied<'_, Q>, Self::Vacant<'_, Q>> {
        use hashbrown::hash_map::RawEntryMut;
        match self.raw_entry_mut().from_key(key.borrow()) {
            RawEntryMut::Occupied(entry) => Entry::Occupied(EntryWrapper { entry, key }),
            RawEntryMut::Vacant(entry) => Entry::Vacant(EntryWrapper { entry, key }),
        }
    }
}
