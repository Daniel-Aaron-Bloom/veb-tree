use core::{
    borrow::Borrow,
    mem::forget,
    ops::{Add, AddAssign, BitAnd, BitAndAssign, Sub, SubAssign},
};

use alloc::collections::VecDeque;
use ghost::phantom;

use crate::{
    collection::{TreeCollection, TreeInsert, TreeRemoveResult, VebTreeCollectionMarker},
    key::{Owned, VebKey},
    tree::VebTreeMarker,
    RemoveResult, VebTree,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// 32 bytes of memory to store all possible `u8`, All operations are `O(1)`.
pub struct ByteSet([u128; 2], ());

pub struct ByteSetMarker;

impl VebTreeMarker<u8, ()> for ByteSetMarker {
    type Tree = ByteSet;
}

impl ByteSet {
    fn array_len(v: [u128; 2]) -> usize {
        v.into_iter().map(u128::count_ones).sum::<u32>() as usize
    }
    fn from_array(v: [u128; 2]) -> Option<Self> {
        if v == [0, 0] {
            None
        } else {
            Some(Self(v, ()))
        }
    }
    pub fn len(&self) -> usize {
        Self::array_len(self.0)
    }
    pub fn lowest(&self) -> u8 {
        (if self.0[0] == 0 {
            debug_assert_ne!(self.0[1], 0);
            128 + self.0[1].trailing_zeros()
        } else {
            self.0[0].trailing_zeros()
        }) as u8
    }
    pub fn highest(&self) -> u8 {
        (if self.0[1] == 0 {
            debug_assert_ne!(self.0[0], 0);
            127 - self.0[0].leading_zeros()
        } else {
            255 - self.0[1].leading_zeros()
        }) as u8
    }
    fn count_below(&self, k: u8) -> usize {
        let mut mask = ByteSet::mask_lower(k);
        mask &= *self;
        Self::array_len(mask)
    }
    /// Create a mask for the bits under bit i
    fn mask_lower(i: u8) -> [u128; 2] {
        let mut k = Self::from_monad(i, ()).0;
        let o;
        (k[0], o) = k[0].overflowing_sub(1);
        if o {
            k[1] -= 1;
        }
        k
    }
    /// Create a mask for the bits under bit i
    fn mask_higher(i: u8) -> [u128; 2] {
        [
            u128::MAX.checked_shl(1 + i as u32).unwrap_or_default(),
            u128::MAX
                .checked_shl(i.saturating_sub(127) as u32)
                .unwrap_or_default(),
        ]
    }
}

struct ByteSetKey(u8);

impl Add<ByteSetKey> for ByteSet {
    type Output = Self;
    fn add(mut self, rhs: ByteSetKey) -> Self::Output {
        self += rhs;
        self
    }
}
impl AddAssign<ByteSetKey> for ByteSet {
    fn add_assign(&mut self, rhs: ByteSetKey) {
        self.0[rhs.0 as usize / 128] |= 1 << (rhs.0 % 128);
    }
}

impl BitAnd<ByteSetKey> for ByteSet {
    type Output = bool;
    fn bitand(self, rhs: ByteSetKey) -> Self::Output {
        self.0[rhs.0 as usize / 128] & 1 << (rhs.0 % 128) != 0
    }
}

impl BitAndAssign<ByteSet> for [u128; 2] {
    fn bitand_assign(&mut self, rhs: ByteSet) {
        self[0] &= rhs.0[0];
        self[1] &= rhs.0[1];
    }
}

impl Sub<ByteSetKey> for ByteSet {
    type Output = Self;
    fn sub(mut self, rhs: ByteSetKey) -> Self::Output {
        self -= rhs;
        self
    }
}
impl SubAssign<ByteSetKey> for ByteSet {
    fn sub_assign(&mut self, rhs: ByteSetKey) {
        self.0[rhs.0 as usize / 128] &= !(1 << (rhs.0 % 128));
    }
}

impl VebTree for ByteSet {
    type Key = u8;
    type Value = ();
    type MinKey<'a> = u8;
    type MaxKey<'a> = u8;
    type EntryKey<'a> = u8;

    fn from_monad(k: Self::Key, v: Self::Value) -> Self {
        Self([0; 2], v) + ByteSetKey(k)
    }
    fn is_monad(&self) -> bool {
        self.len() == 1
    }
    fn len_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
    fn into_monad(self) -> Result<(Self::Key, Self::Value), Self> {
        if self.len() == 1 {
            Ok((self.lowest(), ()))
        } else {
            Err(self)
        }
    }
    fn min_val(&self) -> (Self::MinKey<'_>, &Self::Value) {
        (self.lowest(), &self.1)
    }
    fn min_val_mut(&mut self) -> (Self::MinKey<'_>, &mut Self::Value) {
        (self.lowest(), &mut self.1)
    }
    fn max_val(&self) -> (Self::MinKey<'_>, &Self::Value) {
        (self.highest(), &self.1)
    }
    fn max_val_mut(&mut self) -> (Self::MinKey<'_>, &mut Self::Value) {
        (self.highest(), &mut self.1)
    }

    fn find<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let v = k.into().0;
        if *self & ByteSetKey(v) {
            Some((v, &self.1))
        } else {
            None
        }
    }
    fn find_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let v = k.into().0;
        if *self & ByteSetKey(v) {
            Some((v, &mut self.1))
        } else {
            None
        }
    }
    fn predecessor<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let mut k = Self::mask_lower(k.into().0);
        k &= *self;
        Self::from_array(k).map(|v| (v.highest(), &self.1))
    }
    fn predecessor_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let mut k = Self::mask_lower(k.into().0);
        k &= *self;
        Self::from_array(k).map(|v| (v.highest(), &mut self.1))
    }
    fn successor<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let mut k = Self::mask_higher(k.into().0);
        k &= *self;
        Self::from_array(k).map(|v| (v.lowest(), &self.1))
    }
    fn successor_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let mut k = Self::mask_higher(k.into().0);
        k &= *self;
        Self::from_array(k).map(|v| (v.lowest(), &mut self.1))
    }
    fn insert<Q>(&mut self, k: Q, v: Self::Value) -> Option<(Self::Key, Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let k = k.into().0;
        if *self & ByteSetKey(k) {
            Some((k, v))
        } else {
            *self += ByteSetKey(k);
            None
        }
    }

    fn remove<Q>(mut self, k: Q) -> RemoveResult<Self>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let k = k.into().0;
        if !(self & ByteSetKey(k)) {
            Err(self)
        } else if self.len() == 1 {
            Ok((None, (k, ())))
        } else {
            self -= ByteSetKey(k);
            Ok((Some(self), (k, ())))
        }
    }
    fn remove_min(mut self) -> (Option<Self>, (Self::Key, Self::Value)) {
        let k = self.lowest();
        if self.len() == 1 {
            (None, (k, ()))
        } else {
            self -= ByteSetKey(k);
            (Some(self), (k, ()))
        }
    }
    fn remove_max(mut self) -> (Option<Self>, (Self::Key, Self::Value)) {
        let k = self.highest();
        if self.len() == 1 {
            return (None, (k, ()));
        } else {
            self -= ByteSetKey(k);
            (Some(self), (k, ()))
        }
    }
}

pub trait ListMarker<Tree: VebTree> {
    type List: TreeList<Tree = Tree>;
}

#[phantom]
pub struct ByteMapMarker<#[invariant] ListMarker, #[invariant] Tree>;

impl<K, V, List, Tree> VebTreeCollectionMarker<K, V> for ByteMapMarker<List, Tree>
where
    K: VebKey<High = u8>,
    Tree: VebTreeMarker<K::Low, V>,
    List: ListMarker<Tree::Tree>,
{
    type TreeCollection = ByteMap<List::List>;
}

pub struct ByteMap<L> {
    set: ByteSet,
    list: L,
}

pub type TreeListRemoveResult<TL> = Result<
    (
        Option<(TL, bool)>,
        (
            <<TL as TreeList>::Tree as VebTree>::Key,
            <<TL as TreeList>::Tree as VebTree>::Value,
        ),
    ),
    TL,
>;

pub trait TreeList: Sized {
    type Tree: VebTree;
    fn from_monad(v: Self::Tree) -> Self;

    fn get(&self, i: usize) -> &Self::Tree;
    fn get_mut(&mut self, i: usize) -> &mut Self::Tree;
    fn insert_tree(&mut self, i: usize, v: Self::Tree);
    fn remove_key<F>(self, i: usize, f: F) -> TreeListRemoveResult<Self>
    where
        F: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>;
}
pub trait TreeListMarker<V> {
    type List: TreeList;
}

impl<V: VebTree> TreeList for VecDeque<V> {
    type Tree = V;

    fn from_monad(v: Self::Tree) -> Self {
        VecDeque::from_iter([v])
    }

    fn get(&self, i: usize) -> &Self::Tree {
        &self[i]
    }
    fn get_mut(&mut self, i: usize) -> &mut Self::Tree {
        &mut self[i]
    }
    fn insert_tree(&mut self, i: usize, v: Self::Tree) {
        self.insert(i, v);
    }
    fn remove_key<F>(mut self, i: usize, f: F) -> TreeListRemoveResult<Self>
    where
        F: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>,
    {
        struct PanicHandler<'a, V>(&'a mut VecDeque<V>, usize);
        impl<'a, V> Drop for PanicHandler<'a, V> {
            fn drop(&mut self) {
                forget(self.0.remove(self.1).unwrap());
            }
        }

        // This is safe because we either write over it or forget it
        let tree = unsafe { core::ptr::read(&self[i]) };
        let handler = PanicHandler(&mut self, 0);

        match f(tree) {
            Err(tree) => {
                forget(handler);
                unsafe { core::ptr::write(&mut self[i], tree) };
                Err(self)
            }
            Ok((None, val)) => {
                forget(handler);
                forget(self.remove(i).unwrap());
                if self.is_empty() {
                    Ok((None, val))
                } else {
                    Ok((Some((self, true)), val))
                }
            }
            Ok((Some(tree), val)) => {
                forget(handler);
                unsafe { core::ptr::write(&mut self[i], tree) };
                Ok((Some((self, false)), val))
            }
        }
    }
}

/// All operations are assumed to be `O(1)` complexity
impl<L: TreeList> TreeCollection for ByteMap<L> {
    type High = u8;
    type Tree = L::Tree;

    fn create(h: &u8, tree: Self::Tree) -> Self {
        Self {
            set: ByteSet::from_monad(*h, ()),
            list: L::from_monad(tree),
        }
    }

    fn get(&self, h: &u8) -> Option<&Self::Tree> {
        if !(self.set & ByteSetKey(*h)) {
            return None;
        }
        Some(self.list.get(self.set.count_below(*h)))
    }
    fn get_mut(&mut self, h: &u8) -> Option<&mut Self::Tree> {
        if !(self.set & ByteSetKey(*h)) {
            return None;
        }
        Some(self.list.get_mut(self.set.count_below(*h)))
    }

    fn insert<Q: Borrow<Self::High> + Into<Owned<Self::High>>>(
        &mut self,
        h: Q,
        (l, v): TreeInsert<Self>,
    ) -> Result<Self::High, (Q, Option<TreeInsert<Self>>)> {
        let k = *h.borrow();
        let i = self.set.count_below(k);
        if let Some(_) = self.set.insert(k, ()) {
            self.list.insert_tree(i, VebTree::from_monad(l, v));
            Ok(k)
        } else {
            Err((h, self.list.get_mut(i).insert(l, v)))
        }
    }

    fn remove_key<'a, Q, R>(mut self, h: Q, r: R) -> TreeRemoveResult<Self>
    where
        Q: Borrow<Self::High>,
        R: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>,
    {
        let k = *h.borrow();
        if self.set.find(k).is_none() {
            return Err(self);
        }
        let i = self.set.count_below(k);

        match self.list.remove_key(i, r) {
            Err(list) => {
                self.list = list;
                Err(self)
            }
            Ok((None, v)) => Ok((None, v)),
            Ok((Some((list, removed)), v)) => {
                self.list = list;
                if removed {
                    self.set.remove(k).unwrap();
                }
                Ok((Some(self), v))
            }
        }
    }
}

#[cfg(test)]
mod test {
    use alloc::collections::VecDeque;

    use crate::{collection::TreeCollection, VebTree};

    use super::{ByteMap, ByteSet};

    #[test]
    fn simple_set() {
        let mut set = ByteSet::from_monad(0, ());
        for i in 1..=255u8 {
            assert_eq!(set.lowest(), 0);
            assert_eq!(set.highest(), i - 1);
            assert_eq!(set.predecessor(i), Some((i - 1, &())));
            set.insert(i, ());
            assert_eq!(set.successor(0), Some((1, &())));
            assert_eq!(set.successor(i - 1), Some((i, &())));
            assert_eq!(set.predecessor(i), Some((i - 1, &())));
        }
        assert_eq!(set.highest(), 255);

        let mut set = ByteSet::from_monad(0, ());
        for i in 1..=255u8 {
            assert_eq!(set.successor(i - 1), None);
            assert_eq!(set.lowest(), i - 1);
            assert_eq!(set.highest(), i - 1);
            assert_eq!(set.predecessor(i - 1), None);
            assert_eq!(set.predecessor(i), Some((i - 1, &())));
            set.insert(i, ());
            if i > 1 {
                assert_eq!(set.successor(0), Some((i - 1, &())));
            }
            assert_eq!(set.successor(i - 1), Some((i, &())));
            assert_eq!(set.highest(), i);
            let v = set.remove(i - 1).unwrap();
            set = v.0.unwrap();
            assert_eq!(v.1, ((i - 1), ()));
            assert_eq!(set.successor(0), Some((i, &())));
        }
        assert_eq!(set.lowest(), 255);
        assert_eq!(set.highest(), 255);
    }
    #[test]
    fn simple_map() {
        type Map = ByteMap<VecDeque<ByteSet>>;

        let mut m = Map::create(&0, ByteSet::from_monad(0, ()));
        let _ = m.insert(0, (5, ()));
        let _ = m.insert(1, (5, ()));
    }
}
