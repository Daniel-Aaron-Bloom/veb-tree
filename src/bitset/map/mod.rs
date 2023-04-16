use core::{borrow::Borrow, mem::replace};

use ghost::phantom;

use crate::{
    bitset::ByteSet,
    collection::{
        CollectionKV, TreeCollection, TreeInsertResult, TreeMaybeRemoveResult, TreeRemoveResult,
        VebTreeCollectionMarker,
    },
    key::{MaybeBorrowed, VebKey},
    tree::VebTreeMarker,
    MaybeRemoveResult, RemoveResult, TreeKV, VebTree,
};

pub mod list;

#[phantom]
pub struct ByteCollectionMarker<#[invariant] ListMarker, #[invariant] Val>;

impl<K, V, List, Tree> VebTreeCollectionMarker<K, V> for ByteCollectionMarker<List, Tree>
where
    K: VebKey<Hi = u8>,
    Tree: VebTreeMarker<K::Lo, V>,
    List: list::TreeListMarker<Tree::Tree>,
{
    type TreeCollection = ByteMap<List::List>;
}

pub struct ByteMap<L> {
    set: ByteSet,
    list: L,
}

/// All operations are assumed to be `O(1)` complexity
impl<L: list::TreeList> TreeCollection for ByteMap<L> {
    type Hi = u8;
    type Tree = L::Tree;

    fn create(h: &u8, tree: Self::Tree) -> Self {
        Self {
            set: ByteSet::from_monad(*h, ()),
            list: L::from_monad(tree),
        }
    }

    fn get(&self, h: &u8) -> Option<&Self::Tree> {
        if !(self.set.is_present(*h)) {
            return None;
        }
        Some(self.list.get(self.set.count_below(*h)))
    }
    fn get_mut(&mut self, h: &u8) -> Option<&mut Self::Tree> {
        if !(self.set.is_present(*h)) {
            return None;
        }
        Some(self.list.get_mut(self.set.count_below(*h)))
    }

    fn insert_key(&mut self, h: Self::Hi, (l, v): CollectionKV<Self>) -> TreeInsertResult<Self> {
        let i = self.set.count_below(h);
        let v = if let Some(_) = self.set.insert(h, ()) {
            Err((h, self.list.get_mut(i).insert(l, v)))
        } else {
            self.list.insert_tree(i, VebTree::from_monad(l, v));
            Ok(h)
        };
        v
    }
    fn remove_key<'a, Q, R>(mut self, h: Q, r: R) -> TreeRemoveResult<Self>
    where
        Q: Borrow<Self::Hi>,
        R: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>,
    {
        let k = *h.borrow();
        debug_assert!(self.set.find(k).is_some());
        let i = self.set.count_below(k);

        match self.list.remove_key(i, r) {
            (None, v) => (None, v),
            (Some((list, removed)), v) => {
                self.list = list;
                if removed {
                    debug_assert!(self.set.is_present(k));
                    self.set.unset_bit(k);
                }
                (Some((self, removed)), v)
            }
        }
    }

    fn maybe_remove_key<'a, Q, R>(mut self, h: Q, r: R) -> TreeMaybeRemoveResult<Self>
    where
        Q: Borrow<Self::Hi>,
        R: FnOnce(Self::Tree) -> MaybeRemoveResult<Self::Tree>,
    {
        let k = *h.borrow();
        if self.set.find(k).is_none() {
            return Err(self);
        }
        let i = self.set.count_below(k);

        match self.list.maybe_remove_key(i, r) {
            Err(list) => {
                self.list = list;
                Err(self)
            }
            Ok((None, v)) => Ok((None, v)),
            Ok((Some((list, removed)), v)) => {
                self.list = list;
                if removed {
                    debug_assert!(self.set.is_present(k));
                    self.set.unset_bit(k);
                }
                Ok((Some((self, removed)), v))
            }
        }
    }
}

#[phantom]
pub struct ByteTreeMarker<#[invariant] ListMarker>;

impl<V, List> VebTreeMarker<u8, V> for ByteTreeMarker<List>
where
    List: list::ListMarker<V>,
{
    type Tree = ByteMap<List::List>;
}

impl<L: list::List> VebTree for ByteMap<L> {
    type Key = u8;
    type Value = L::Value;
    fn from_monad(key: Self::Key, val: Self::Value) -> Self {
        let mut list = L::create();
        list.insert_value(0, val);
        Self {
            set: ByteSet::from_monad(key, ()),
            list,
        }
    }
    fn is_monad(&self) -> bool {
        self.list.len() == 1
    }
    fn into_monad(mut self) -> Result<TreeKV<Self>, Self> {
        match self.set.into_monad() {
            Ok((k, ())) => {
                let v = self.list.remove_value(0);
                debug_assert!(v.0.is_none());
                Ok((k, v.1))
            }
            Err(set) => {
                self.set = set;
                Err(self)
            }
        }
    }
    fn min_val(&self) -> (MaybeBorrowed<Self::Key>, &Self::Value) {
        (self.set.min_val().0, self.list.get(0))
    }
    fn min_val_mut(&mut self) -> (MaybeBorrowed<Self::Key>, &mut Self::Value) {
        (self.set.min_val().0, self.list.get_mut(0))
    }
    fn max_val(&self) -> (MaybeBorrowed<Self::Key>, &Self::Value) {
        (self.set.max_val().0, self.list.get(self.list.len() - 1))
    }
    fn max_val_mut(&mut self) -> (MaybeBorrowed<Self::Key>, &mut Self::Value) {
        (self.set.max_val().0, self.list.get_mut(self.list.len() - 1))
    }
    fn find<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = *k.into();
        let (k, ()) = self.set.find(k)?;
        let i = self.set.count_below(*k.borrow());
        Some((k, self.list.get(i)))
    }
    fn find_mut<'a, Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = *k.into();
        let (k, ()) = self.set.find(k)?;
        let i = self.set.count_below(*k.borrow());
        Some((k, self.list.get_mut(i)))
    }
    fn predecessor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = *k.into();
        let (k, ()) = self.set.predecessor(k)?;
        let i = self.set.count_below(*k.borrow());
        Some((k, self.list.get(i)))
    }
    fn predecessor_mut<'a, Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = *k.into();
        let (k, ()) = self.set.predecessor(k)?;
        let i = self.set.count_below(*k.borrow());
        Some((k, self.list.get_mut(i)))
    }
    fn successor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = *k.into();
        let (k, ()) = self.set.successor(k)?;
        let i = self.set.count_below(*k.borrow());
        Some((k, self.list.get(i)))
    }
    fn successor_mut<'a, Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = *k.into();
        let (k, ()) = self.set.successor(k)?;
        let i = self.set.count_below(*k.borrow());
        Some((k, self.list.get_mut(i)))
    }
    fn insert(&mut self, k: Self::Key, v: Self::Value) -> Option<TreeKV<Self>> {
        match self.set.insert(k, ()) {
            Some((k, ())) => {
                let i = self.set.count_below(k);
                let v = replace(self.list.get_mut(i), v);
                Some((k, v))
            }
            None => {
                let i = self.set.count_below(k);
                self.list.insert_value(i, v);
                None
            }
        }
    }
    fn remove<'a, Q>(mut self, k: Q) -> MaybeRemoveResult<Self>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = *k.into();
        let i = self.set.count_below(k);
        match self.set.remove(k) {
            Err(set) => {
                self.set = set;
                Err(self)
            }
            Ok((Some(set), (k, ()))) => {
                let (list, v) = self.list.remove_value(i);
                let list = list.unwrap();
                Ok((Some(Self { list, set }), (k, v)))
            }
            Ok((None, (k, ()))) => {
                let (list, v) = self.list.remove_value(i);
                debug_assert!(list.is_none());
                Ok((None, (k, v)))
            }
        }
    }

    fn remove_min(self) -> RemoveResult<Self> {
        let i = self.set.count_below(*self.set.min_val().0);
        let (set, (k, ())) = self.set.remove_min();
        let (list, v) = self.list.remove_value(i);
        match (set, list) {
            (Some(set), Some(list)) => (Some(Self { list, set }), (k, v)),
            (None, None) => (None, (k, v)),
            _ => unreachable!(),
        }
    }
    fn remove_max(self) -> RemoveResult<Self> {
        let i = self.set.count_below(*self.set.max_val().0);
        let (set, (k, ())) = self.set.remove_max();
        let (list, v) = self.list.remove_value(i);
        match (set, list) {
            (Some(set), Some(list)) => (Some(Self { list, set }), (k, v)),
            (None, None) => (None, (k, v)),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod test {
    use alloc::collections::VecDeque;

    use crate::{collection::TreeCollection, VebTree};

    use super::{ByteMap, ByteSet};
    #[test]
    fn simple_map() {
        type Map = ByteMap<VecDeque<ByteSet>>;

        let mut m = Map::create(&0, ByteSet::from_monad(0, ()));
        let _ = m.insert_key(0, (5, ()));
        let _ = m.insert_key(1, (5, ()));
    }
}
