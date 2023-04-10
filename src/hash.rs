use core::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
};

use ghost::phantom;
use hashbrown::hash_map::DefaultHashBuilder;
use hashbrown::HashMap;

use crate::{
    key::{Owned, VebKey},
    tree::{TreeCollectionMarker, VebTreeMarker},
    RemoveResult, VebTree,
};

#[phantom]
pub struct HashMapMarker<#[invariant] Tree = (), #[invariant] S = DefaultHashBuilder>;

impl<K, V, Tree, S> TreeCollectionMarker<K, V> for HashMapMarker<Tree, S>
where
    K: VebKey,
    K::High: 'static + Hash,
    Tree: VebTreeMarker<K::Low, V>,
    Tree::Tree: 'static,
    S: 'static + BuildHasher + Default,
{
    type TreeCollection = HashMap<K::High, Tree::Tree, S>;
}

impl<K, V, S> VebTreeMarker<K, V> for HashMapMarker<(), S>
where
    K: Ord + Clone + Hash,
    V: 'static,
    S: 'static + BuildHasher + Default,
{
    type Tree = HashMap<K, V, S>;
}

impl<K: Clone + Ord + Hash, V, S: BuildHasher + Default> VebTree for HashMap<K, V, S> {
    type Key = K;
    type Value = V;
    type MinKey<'a> = &'a K where (K, V, S): 'a;
    type MaxKey<'a> = &'a K where (K, V, S): 'a;
    type EntryKey<'a> = &'a K where (K, V, S): 'a;

    fn from_monad(key: Self::Key, val: Self::Value) -> Self {
        let mut v = Self::with_capacity_and_hasher(1, S::default());
        v.insert(key, val);
        v
    }

    fn is_monad(&self) -> bool {
        self.len() == 1
    }

    fn len_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }

    fn into_monad(self) -> Result<(Self::Key, Self::Value), Self> {
        if self.len() == 1 {
            Ok(self.into_iter().next().unwrap())
        } else {
            Err(self)
        }
    }

    fn min_val(&self) -> (Self::MinKey<'_>, &Self::Value) {
        let mut iter = self.iter();
        let v = iter.next().unwrap();
        iter.fold(v, |v, n| if v.0 < n.0 { v } else { n })
    }

    fn min_val_mut(&mut self) -> (Self::MinKey<'_>, &mut Self::Value) {
        let mut iter = self.iter_mut();
        let v = iter.next().unwrap();
        iter.fold(v, |v, n| if v.0 < n.0 { v } else { n })
    }

    fn max_val(&self) -> (Self::MaxKey<'_>, &Self::Value) {
        let mut iter = self.iter();
        let v = iter.next().unwrap();
        iter.fold(v, |v, n| if v.0 > n.0 { v } else { n })
    }

    fn max_val_mut(&mut self) -> (Self::MaxKey<'_>, &mut Self::Value) {
        let mut iter = self.iter_mut();
        let v = iter.next().unwrap();
        iter.fold(v, |v, n| if v.0 > n.0 { v } else { n })
    }

    fn find<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.get_key_value(k.borrow())
    }

    fn find_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.get_key_value_mut(k.borrow())
    }

    fn predecessor<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.iter().fold(None, |prev, cur| {
            if let Some(prev) = prev {
                if prev.0 < cur.0 && cur.0 < k.borrow() {
                    Some(cur)
                } else {
                    Some(prev)
                }
            } else if cur.0 < k.borrow() {
                Some(cur)
            } else {
                None
            }
        })
    }

    fn predecessor_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.iter_mut().fold(None, |prev, cur| {
            if let Some(prev) = prev {
                if prev.0 < cur.0 && cur.0 < k.borrow() {
                    Some(cur)
                } else {
                    Some(prev)
                }
            } else if cur.0 < k.borrow() {
                Some(cur)
            } else {
                None
            }
        })
    }

    fn successor<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.iter().fold(None, |prev, cur| {
            if let Some(prev) = prev {
                if prev.0 > cur.0 && cur.0 > k.borrow() {
                    Some(cur)
                } else {
                    Some(prev)
                }
            } else if cur.0 > k.borrow() {
                Some(cur)
            } else {
                None
            }
        })
    }

    fn successor_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        self.iter_mut().fold(None, |prev, cur| {
            if let Some(prev) = prev {
                if prev.0 > cur.0 && cur.0 > k.borrow() {
                    Some(cur)
                } else {
                    Some(prev)
                }
            } else if cur.0 > k.borrow() {
                Some(cur)
            } else {
                None
            }
        })
    }

    fn insert<Q>(&mut self, k: Q, v: Self::Value) -> Option<(Self::Key, Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        use hashbrown::hash_map::Entry;
        match self.entry(k.into().0) {
            Entry::Occupied(e) => Some(e.replace_entry(v)),
            Entry::Vacant(e) => {
                e.insert(v);
                None
            }
        }
    }

    fn remove<Q>(&mut self, k: Q) -> RemoveResult<(Self::Key, Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        use hashbrown::hash_map::Entry;
        match (self.len(), self.entry(k.into().0)) {
            (1, Entry::Occupied(_)) => RemoveResult::Monad,
            (_, Entry::Occupied(e)) => RemoveResult::Removed(e.remove_entry()),
            (_, Entry::Vacant(_)) => RemoveResult::NotPresent,
        }
    }

    fn remove_min(&mut self) -> Option<(Self::Key, Self::Value)> {
        if self.len() == 1 {
            None
        } else {
            self.remove_entry(&self.min_val().0.clone())
        }
    }

    fn remove_max(&mut self) -> Option<(Self::Key, Self::Value)> {
        if self.len() == 1 {
            None
        } else {
            self.remove_entry(&self.max_val().0.clone())
        }
    }
}

#[cfg(test)]
mod test {
    use hashbrown::HashMap;

    use crate::VebTree;

    #[test]
    fn simple() {
        type U16Tree = HashMap<u16, ()>;
        let mut v = U16Tree::from_monad(10, ());

        assert_eq!(v.find(10), Some((&10, &())));
        assert_eq!(v.find(11), None);
        v.insert(13, ());
        assert_eq!(v.find(13), Some((&13, &())));
        assert_eq!(v.predecessor(14), Some((&13, &())));
        assert_eq!(v.min_val(), (&10, &()));
        assert_eq!(v.max_val(), (&13, &()));

        v.insert(5, ());
        assert_eq!(v.min_val(), (&5, &()));
    }
}
