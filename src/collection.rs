use core::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
};

use hashbrown::{
    HashMap,
};

use crate::{key::Owned, VebTree};
use crate::{key::VebKey, RemoveResult};

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

pub type TreeRemoveResult<TC> = Result<
    (
        Option<TC>,
        (
            <<TC as TreeCollection>::Tree as VebTree>::Key,
            <<TC as TreeCollection>::Tree as VebTree>::Value,
        ),
    ),
    TC,
>;

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
    fn insert<Q>(&mut self, h: Q, l: <Self::Tree as VebTree>::Key, v: <Self::Tree as VebTree>::Value) -> Result<Self::High, (Q, Option<(<Self::Tree as VebTree>::Key, <Self::Tree as VebTree>::Value)>)>
    where Q: Borrow<Self::High> + Into<Owned<Self::High>>;

    /// Remove a value from a tree contained within.
    ///
    /// If the tree containing the value is a monad, it will be removed from
    /// the collection. If there are no remaning trees the entire collection
    /// is erased.
    fn remove_key<'a, Q, R>(self, h: Q, r: R) -> TreeRemoveResult<Self>
    where
        Q: Borrow<Self::High>,
        R: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>;
}

impl<High, V, S> TreeCollection for HashMap<High, V, S>
where
    High: 'static + Clone + Eq + Hash,
    V: 'static + VebTree,
    S: 'static + BuildHasher + Default,
{
    type High = High;
    type Tree = V;

    fn create(h: &Self::High, tree: Self::Tree) -> Self {
        let v = HashMap::from_iter([(h.clone(), tree)]);
        debug_assert_eq!(v.len(), 1);
        debug_assert!(v.contains_key(h));

        v
    }

    fn get(&self, h: &Self::High) -> Option<&Self::Tree> {
        self.get(h)
    }
    fn get_mut(&mut self, h: &Self::High) -> Option<&mut Self::Tree> {
        self.get_mut(h)
    }

    fn insert<Q>(&mut self, h: Q, l: <Self::Tree as VebTree>::Key, v: <Self::Tree as VebTree>::Value) -> Result<Self::High, (Q, Option<(<Self::Tree as VebTree>::Key, <Self::Tree as VebTree>::Value)>)>
    where Q: Borrow<Self::High> + Into<Owned<Self::High>>{
        use hashbrown::hash_map::RawEntryMut;
        let mut entry = match self.raw_entry_mut().from_key(h.borrow()) {
            RawEntryMut::Vacant(entry) => {
                return Ok(entry.insert(h.into().0, V::from_monad(l, v)).0.clone())
            },
            RawEntryMut::Occupied(entry) => entry,
        };
        let v = entry.get_mut().insert(l, v);
        Err((h, v))
    }

    fn remove_key<'a, Q, R>(mut self, h: Q, r: R) -> TreeRemoveResult<Self>
    where
        Q: Borrow<Self::High>,
        R: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>,
    {
        use hashbrown::hash_map::RawEntryMut;
        let entry = match self.raw_entry_mut().from_key(h.borrow()) {
            RawEntryMut::Vacant(_) => return Err(self),
            RawEntryMut::Occupied(entry) => entry,
        };

        let mut val = None;
        entry.replace_entry_with(|_k, v| match r(v) {
            Err(v) => Some(v),
            Ok((v, rval)) => {
                val = Some(rval);
                v
            }
        });
        let val = val.unwrap();
        Ok(if self.is_empty() {
            (None, val)
        } else {
            (Some(self), val)
        })
    }
}
