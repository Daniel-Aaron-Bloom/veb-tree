use core::{
    borrow::Borrow,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign},
};

use crate::{
    collection::{Entry, TreeCollection, TreeRemoveResult},
    key::Owned,
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
        if v == [0,0] {
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

impl BitOr<u8> for ByteSet {
    type Output = Self;
    fn bitor(mut self, rhs: u8) -> Self::Output {
        self |= rhs;
        self
    }
}
impl BitOrAssign<u8> for ByteSet {
    fn bitor_assign(&mut self, rhs: u8) {
        self.0[rhs as usize / 128] |= 1 << (rhs % 128);
    }
}

impl BitAnd<u8> for ByteSet {
    type Output = bool;
    fn bitand(self, rhs: u8) -> Self::Output {
        self.0[rhs as usize / 128] & 1 << (rhs % 128) != 0
    }
}

impl BitAndAssign for ByteSet {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0[0] &= rhs.0[0];
        self.0[1] &= rhs.0[1];
    }
}
impl BitAndAssign<ByteSet> for [u128; 2] {
    fn bitand_assign(&mut self, rhs: ByteSet) {
        self[0] &= rhs.0[0];
        self[1] &= rhs.0[1];
    }
}

impl BitXor<u8> for ByteSet {
    type Output = Self;
    fn bitxor(mut self, rhs: u8) -> Self::Output {
        self ^= rhs;
        self
    }
}
impl BitXorAssign<u8> for ByteSet {
    fn bitxor_assign(&mut self, rhs: u8) {
        self.0[rhs as usize / 128] &= !(1 << (rhs % 128));
    }
}

impl VebTree for ByteSet {
    type Key = u8;
    type Value = ();
    type MinKey<'a> = u8;
    type MaxKey<'a> = u8;
    type EntryKey<'a> = u8;

    fn from_monad(k: Self::Key, v: Self::Value) -> Self {
        Self([0; 2], v) | k
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
        if *self & v {
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
        if *self & v {
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
        if *self & k {
            Some((k, v))
        } else {
            *self |= k;
            None
        }
    }

    fn remove<Q>(&mut self, k: Q) -> RemoveResult<(Self::Key, Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        if self.len() == 1 {
            return RemoveResult::Monad;
        }
        let k = k.into().0;
        if *self & k {
            *self ^= k;
            RemoveResult::Removed((k, ()))
        } else {
            RemoveResult::NotPresent
        }
    }
    fn remove_min(&mut self) -> Option<(Self::Key, Self::Value)> {
        if self.len() == 1 {
            return None;
        }
        let k = self.lowest();
        *self ^= k;
        Some((k, ()))
    }
    fn remove_max(&mut self) -> Option<(Self::Key, Self::Value)> {
        if self.len() == 1 {
            return None;
        }
        let k = self.highest();
        *self ^= k;
        Some((k, ()))
    }
}

pub struct ByteMap<L> {
    set: ByteSet,
    list: L,
}

pub trait TreeList {
    type Tree: VebTree;
    fn from_monad(v: Self::Tree) -> Self;

    fn get(&self, i: usize) -> &Self::Tree;
    fn get_mut(&self, i: usize) -> &mut Self::Tree;
}

pub struct Vacant;
pub struct Occupied<'a, Q, L> {
    key: Q,
    list: &'a mut L,
    index: usize,
}

/// All operations are assumed to be `O(1)` complexity
impl<L: TreeList> TreeCollection for ByteMap<L> {
    type High = u8;
    type Tree = L::Tree;

    type Occupied<'a, Q> = Occupied<'a, Q, L>
    where Self: 'a;
    type Vacant<'a, Q> = Vacant
    where Self: 'a;

    fn create(h: &u8, tree: Self::Tree) -> Self {
        Self {
            set: ByteSet::from_monad(*h, ()),
            list: L::from_monad(tree)
        }
    }

    fn get(&self, h: &u8) -> Option<&Self::Tree> {
        if !(self.set & *h) {
            return None
        }
        let mut v = ByteSet::mask_lower(*h);
        v &= self.set;
        Some(self.list.get(ByteSet::array_len(v)))
    }
    fn get_mut(&mut self, h: &u8) -> Option<&mut Self::Tree> {
        if !(self.set & *h) {
            return None
        }
        let mut v = ByteSet::mask_lower(*h);
        v &= self.set;
        Some(self.list.get_mut(ByteSet::array_len(v)))
    }

    fn entry<Q: Borrow<u8>>(
        &mut self,
        key: Q,
    ) -> Entry<Self::Occupied<'_, Q>, Self::Vacant<'_, Q>> {
        let mut v = ByteSet::mask_lower(*key.borrow());
        v &= self.set;
        let index = ByteSet::array_len(v);

        if self.set & *key.borrow() {
            Entry::Occupied(Occupied{
                key,
                list: &mut self.list,
                index,
            })
        } else {
            Entry::Vacant(Vacant)
        }
    }

    fn deref<'a, 'b, Q>(v: &'a mut Occupied<'b, Q, L>) -> (&'a mut u8, &'a mut Self::Tree) {
        todo!()
    }

    fn decompose<'a, Q>(v: Self::Occupied<'a, Q>) -> (Q, &'a mut Self::Tree) {
        todo!()
    }

    fn remove<'a, Q>(o: Occupied<'a, Q, L>) -> TreeRemoveResult<Q, u8, Self::Tree> {
        todo!()
    }

    fn key<'a, 'b, Q: Borrow<u8>>(v: &'a Vacant) -> &'a u8 {
        todo!()
    }

    fn insert<'a, Q: Borrow<u8> + Into<Owned<u8>>>(
        v: Vacant,
        tree: Self::Tree,
    ) -> &'a mut Self::Tree {
        todo!()
    }
}

#[cfg(test)]
mod test {
    use crate::VebTree;

    use super::ByteSet;

    #[test]
    fn simple() {
        let mut set = ByteSet::from_monad(0, ());
        for i in 1..=255u8 {
            assert_eq!(set.lowest(), 0);
            assert_eq!(set.highest(), i - 1);
            assert_eq!(set.predecessor(i), Some((i - 1, &())));
            set |= i;
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
            set |= i;
            if i > 1 {
                assert_eq!(set.successor(0), Some((i-1, &())));
            }
            assert_eq!(set.successor(i - 1), Some((i, &())));
            assert_eq!(set.highest(), i);
            set ^= i - 1;
            assert_eq!(set.successor(0), Some((i, &())));
        }
        assert_eq!(set.lowest(), 255);
        assert_eq!(set.highest(), 255);
    }
}
