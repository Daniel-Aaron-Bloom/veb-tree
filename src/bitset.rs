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
    pub fn len(&self) -> usize {
        self.0.into_iter().map(u128::count_ones).sum::<u32>() as usize
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
        let k = k.into().0;
        let mut k = Self::from_monad(k, ());
        let o;
        (k.0[0], o) = k.0[0].overflowing_sub(1);
        if o {
            k.0[1] -= 1;
        }
        k &= *self;

        if k.len() == 0 {
            None
        } else {
            Some((k.highest(), &self.1))
        }
    }
    fn predecessor_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let k = k.into().0;
        let mut k = Self::from_monad(k, ());
        let o;
        (k.0[0], o) = k.0[0].overflowing_sub(1);
        if o {
            k.0[1] -= 1;
        }
        k &= *self;

        if k.len() == 0 {
            None
        } else {
            Some((k.highest(), &mut self.1))
        }
    }
    fn successor<Q>(&self, k: Q) -> Option<(Self::EntryKey<'_>, &Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let k = k.into().0;
        let mut k = Self(
            [
                u128::MAX.checked_shl(1 + k as u32).unwrap_or_default(),
                u128::MAX
                    .checked_shl(k.saturating_sub(127) as u32)
                    .unwrap_or_default(),
            ],
            (),
        );
        k &= *self;

        if k.len() == 0 {
            None
        } else {
            Some((k.highest(), &self.1))
        }
    }
    fn successor_mut<Q>(&mut self, k: Q) -> Option<(Self::EntryKey<'_>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key> + Into<Owned<Self::Key>>,
    {
        let k = k.into().0;
        let mut k = Self(
            [
                u128::MAX.checked_shl(1 + k as u32).unwrap_or_default(),
                u128::MAX
                    .checked_shl(k.saturating_sub(127) as u32)
                    .unwrap_or_default(),
            ],
            (),
        );
        k &= *self;

        if k.len() == 0 {
            None
        } else {
            Some((k.highest(), &mut self.1))
        }
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

pub struct ByteMap<V> {
    set: ByteSet,
    values: V,
}

trait TreeList {
    type Tree: VebTree;
}

/// All operations are assumed to be `O(1)` complexity
// impl<V: TreeList> TreeCollection for ByteMap<V>{
//     type High = u8;
//     type Tree = V::Tree;
// }

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
            assert_eq!(set.successor(i - 1), Some((i, &())));
            assert_eq!(set.highest(), i);
            set ^= i - 1;
        }
        assert_eq!(set.lowest(), 255);
        assert_eq!(set.highest(), 255);
    }
}
