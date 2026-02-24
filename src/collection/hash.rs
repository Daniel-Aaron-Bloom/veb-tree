use core::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
};

use ghost::phantom;
use hashbrown::DefaultHashBuilder;
use hashbrown::HashMap;

use crate::{
    collection::{
        CollectionKV, TreeCollection, TreeInsertResult, TreeMaybeRemoveResult, TreeRemoveResult,
        VebTreeCollectionMarker,
    },
    key::VebKey,
    tree::VebTreeMarker,
    MaybeRemoveResult, RemoveResult, VebTree,
};

#[phantom]
pub struct HashMapMarker<Tree = (), S = DefaultHashBuilder>;

impl<K, V, Tree, S> VebTreeCollectionMarker<K, V> for HashMapMarker<Tree, S>
where
    K: VebKey,
    K::Hi: Clone + Hash,
    Tree: VebTreeMarker<K::Lo, V>,
    S: BuildHasher + Default,
{
    type TreeCollection = HashMap<K::Hi, Tree::Tree, S>;
}

impl<Hi, V, S> TreeCollection for HashMap<Hi, V, S>
where
    Hi: Clone + Eq + Hash,
    V: VebTree,
    S: BuildHasher + Default,
{
    type Hi = Hi;
    type Tree = V;

    fn create(h: &Self::Hi, tree: Self::Tree) -> Self {
        let v = HashMap::from_iter([(h.clone(), tree)]);
        debug_assert_eq!(v.len(), 1);
        debug_assert!(v.contains_key(h));

        v
    }

    fn get(&self, h: &Self::Hi) -> Option<&Self::Tree> {
        self.get(h)
    }
    fn get_mut(&mut self, h: &Self::Hi) -> Option<&mut Self::Tree> {
        self.get_mut(h)
    }

    fn insert_key(&mut self, h: Self::Hi, (l, v): CollectionKV<Self>) -> TreeInsertResult<Self> {
        use hashbrown::hash_map::RawEntryMut;
        let mut entry = match self.raw_entry_mut().from_key(&h) {
            RawEntryMut::Vacant(entry) => {
                return Ok(entry.insert(h, V::from_monad(l, v)).0.clone())
            }
            RawEntryMut::Occupied(entry) => entry,
        };
        let v = entry.get_mut().insert(l, v);
        Err((h, v))
    }

    fn remove_key<'a, Q, R>(mut self, h: Q, r: R) -> TreeRemoveResult<Self>
    where
        Q: Borrow<Self::Hi>,
        R: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>,
    {
        use hashbrown::hash_map::RawEntryMut;
        let entry = match self.raw_entry_mut().from_key(h.borrow()) {
            RawEntryMut::Vacant(_) => unreachable!(),
            RawEntryMut::Occupied(entry) => entry,
        };

        let mut val = None;
        let entry = entry.replace_entry_with(|_k, v| {
            let (v, rval) = r(v);
            val = Some(rval);
            v
        });
        let removed = matches!(entry, RawEntryMut::Vacant(_));
        // SAFETY: val is always set inside replace_entry_with closure
        let val: (<V as VebTree>::Key, <V as VebTree>::Value) =
            val.expect("val is always set in replace_entry_with");
        if self.is_empty() {
            (None, val)
        } else {
            (Some((self, removed)), val)
        }
    }

    fn maybe_remove_key<'a, Q, R>(mut self, h: Q, r: R) -> TreeMaybeRemoveResult<Self>
    where
        Q: Borrow<Self::Hi>,
        R: FnOnce(Self::Tree) -> MaybeRemoveResult<Self::Tree>,
    {
        use hashbrown::hash_map::RawEntryMut;
        let entry = match self.raw_entry_mut().from_key(h.borrow()) {
            RawEntryMut::Vacant(_) => return Err(self),
            RawEntryMut::Occupied(entry) => entry,
        };

        let mut val = None;
        let entry = entry.replace_entry_with(|_k, v| match r(v) {
            Err(v) => Some(v),
            Ok((v, rval)) => {
                val = Some(rval);
                v
            }
        });
        let removed = matches!(entry, RawEntryMut::Vacant(_));
        match (val, self.is_empty()) {
            (Some(val), true) => Ok((None, val)),
            (Some(val), false) => Ok((Some((self, removed)), val)),
            (None, false) => Err(self),
            (None, true) => unreachable!(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    type U8Tree = HashMap<u8, crate::bitset::ByteSet>;

    #[test]
    fn hash_collection_create() {
        use crate::bitset::ByteSet;
        let tree = ByteSet::from_monad(5, ());
        let collection = U8Tree::create(&10, tree);

        assert_eq!(collection.len(), 1);
        assert!(collection.get(&10).is_some());
        assert!(collection.get(&11).is_none());
    }

    #[test]
    fn hash_collection_get_operations() {
        use crate::bitset::ByteSet;
        let tree1 = ByteSet::from_monad(5, ());
        let mut collection = U8Tree::create(&10, tree1);

        // Get existing key
        assert!(collection.get(&10).is_some());
        assert!(collection.get_mut(&10).is_some());

        // Get non-existing key
        assert!(collection.get(&20).is_none());
        assert!(collection.get_mut(&20).is_none());
    }

    #[test]
    fn hash_collection_insert_new_key() {
        use crate::bitset::ByteSet;
        let tree1 = ByteSet::from_monad(5, ());
        let mut collection = U8Tree::create(&10, tree1);

        // Insert new key
        let result = collection.insert_key(20, (7, ()));
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 20);

        assert_eq!(collection.len(), 2);
        assert!(collection.get(&20).is_some());
    }

    #[test]
    fn hash_collection_insert_existing_key() {
        use crate::bitset::ByteSet;
        let tree1 = ByteSet::from_monad(5, ());
        let mut collection = U8Tree::create(&10, tree1);

        // Insert into existing tree
        let result = collection.insert_key(10, (7, ()));
        assert!(result.is_err());
        let (key, val) = result.unwrap_err();
        assert_eq!(key, 10);
        assert!(val.is_none()); // New value inserted into tree
    }

    #[test]
    fn hash_collection_remove_last_element() {
        use crate::bitset::ByteSet;
        let tree = ByteSet::from_monad(5, ());
        let collection = U8Tree::create(&10, tree);

        // Remove the only element
        let (result, (key, _val)) = collection.remove_key(&10, |t| t.remove(5).unwrap());
        assert!(result.is_none()); // Collection should be empty
        assert_eq!(key, 5);
    }

    #[test]
    fn hash_collection_remove_from_multi_element() {
        use crate::bitset::ByteSet;
        let mut tree1 = ByteSet::from_monad(5, ());
        tree1.insert(6, ());
        let mut collection = U8Tree::create(&10, tree1);

        collection.insert_key(20, (7, ())).unwrap();

        assert_eq!(collection.len(), 2);

        // Remove element from one tree (but tree still has elements)
        let (result, (key, _val)) = collection.remove_key(&10, |t| {
            let (remaining, val) = t.remove(5).unwrap();
            (remaining, val)
        });

        let (collection, removed) = result.unwrap();
        assert_eq!(collection.len(), 2); // Still 2 trees
        assert!(!removed); // Tree not removed, still has element 6
        assert_eq!(key, 5);
    }

    #[test]
    fn hash_collection_maybe_remove_not_found() {
        use crate::bitset::ByteSet;
        let tree = ByteSet::from_monad(5, ());
        let collection = U8Tree::create(&10, tree);

        // Try to remove from non-existing key
        let result = collection.maybe_remove_key(&20, |t| t.remove(5));
        assert!(result.is_err()); // Key 20 doesn't exist
    }

    #[test]
    fn hash_collection_maybe_remove_element_not_in_tree() {
        use crate::bitset::ByteSet;
        let tree = ByteSet::from_monad(5, ());
        let collection = U8Tree::create(&10, tree);

        // Try to remove element that doesn't exist in the tree
        let result = collection.maybe_remove_key(&10, |t| t.remove(99));
        assert!(result.is_err()); // Element 99 not in tree
    }

    #[test]
    fn hash_collection_maybe_remove_success() {
        use crate::bitset::ByteSet;
        let tree = ByteSet::from_monad(5, ());
        let collection = U8Tree::create(&10, tree);

        let result = collection.maybe_remove_key(&10, |t| t.remove(5));
        assert!(result.is_ok());
        let (coll, (key, _val)) = result.unwrap();
        assert!(coll.is_none()); // Collection empty after removing only element
        assert_eq!(key, 5);
    }
}
