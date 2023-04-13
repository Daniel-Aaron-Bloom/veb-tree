use core::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
};

use ghost::phantom;
use hashbrown::hash_map::DefaultHashBuilder;
use hashbrown::HashMap;

use crate::{
    collection::{
        CollectionKV, TreeCollection, TreeInsertResult, TreeMaybeRemoveResult, TreeRemoveResult,
        VebTreeCollectionMarker,
    },
    key::{MaybeBorrowed, VebKey},
    tree::VebTreeMarker,
    MaybeRemoveResult, RemoveResult, VebTree,
};

#[phantom]
pub struct HashMapMarker<#[invariant] Tree = (), #[invariant] S = DefaultHashBuilder>;

impl<K, V, Tree, S> VebTreeCollectionMarker<K, V> for HashMapMarker<Tree, S>
where
    K: VebKey,
    K::Hi: Hash,
    Tree: VebTreeMarker<K::Lo, V>,
    S: BuildHasher + Default,
{
    type TreeCollection = HashMap<K::Hi, Tree::Tree, S>;
}

impl<High, V, S> TreeCollection for HashMap<High, V, S>
where
    High: Clone + Eq + Hash,
    V: VebTree,
    S: BuildHasher + Default,
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

    fn insert_key<'a, Q>(
        &'a mut self,
        h: Q,
        (l, v): CollectionKV<Self>,
    ) -> TreeInsertResult<'a, Self>
    where
        Q: Into<MaybeBorrowed<'a, Self::High>>,
        Self::High: 'a,
    {
        let h = h.into();
        use hashbrown::hash_map::RawEntryMut;
        let mut entry = match self.raw_entry_mut().from_key(&*h) {
            RawEntryMut::Vacant(entry) => {
                return Ok(MaybeBorrowed::Borrowed(
                    entry.insert(h.into_or_clone(), V::from_monad(l, v)).0,
                ))
            }
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
        let val = val.unwrap();
        if self.is_empty() {
            (None, val)
        } else {
            (Some((self, removed)), val)
        }
    }

    fn maybe_remove_key<'a, Q, R>(mut self, h: Q, r: R) -> TreeMaybeRemoveResult<Self>
    where
        Q: Borrow<Self::High>,
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
    // use hashbrown::HashMap;

    // use crate::VebTree;

    // #[test]
    // fn simple() {
    //     type U16Tree = HashMap<u16, ()>;
    //     let mut v = U16Tree::from_monad(10, ());

    //     assert_eq!(v.find(10), Some((&10, &())));
    //     assert_eq!(v.find(11), None);
    //     v.insert(13, ());
    //     assert_eq!(v.find(13), Some((&13, &())));
    //     assert_eq!(v.predecessor(14), Some((&13, &())));
    //     assert_eq!(v.min_val(), (&10, &()));
    //     assert_eq!(v.max_val(), (&13, &()));

    //     v.insert(5, ());
    //     assert_eq!(v.min_val(), (&5, &()));
    // }
}
