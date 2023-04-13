use core::ops::BitAndAssign;

use crate::{key::MaybeBorrowed, tree::VebTreeMarker, MaybeRemoveResult, VebTree};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// 32 bytes of memory to store all possible `u8`, All operations are `O(1)`.
pub struct ByteSet([u128; 2], ());

pub struct ByteSetMarker;

impl VebTreeMarker<u8, ()> for ByteSetMarker {
    type Tree = ByteSet;
}

impl ByteSet {
    #[inline(always)]
    fn array_len(v: [u128; 2]) -> usize {
        (v[0].count_ones() + v[1].count_ones()) as usize
    }
    #[inline(always)]
    fn from_array(v: [u128; 2]) -> Option<Self> {
        if v == [0, 0] {
            None
        } else {
            Some(Self(v, ()))
        }
    }
    #[inline(always)]
    pub fn len(&self) -> usize {
        Self::array_len(self.0)
    }
    #[inline(always)]
    pub fn lowest(&self) -> u8 {
        (if self.0[0] == 0 {
            debug_assert_ne!(self.0[1], 0);
            128 + self.0[1].trailing_zeros()
        } else {
            self.0[0].trailing_zeros()
        }) as u8
    }
    #[inline(always)]
    pub fn highest(&self) -> u8 {
        (if self.0[1] == 0 {
            debug_assert_ne!(self.0[0], 0);
            127 - self.0[0].leading_zeros()
        } else {
            255 - self.0[1].leading_zeros()
        }) as u8
    }
    #[inline(always)]
    pub(crate) fn count_below(&self, k: u8) -> usize {
        let mut mask = ByteSet::mask_lower(k);
        mask &= *self;
        Self::array_len(mask)
    }
    /// Create a mask for the bits under bit i
    #[inline(always)]
    fn mask_lower(i: u8) -> [u128; 2] {
        let i = i as u32;
        [
            u128::MAX
                .checked_shr(128u32.saturating_sub(i))
                .unwrap_or_default(),
            u128::MAX
                .checked_shr(256u32.saturating_sub(i))
                .unwrap_or_default(),
        ]
    }
    /// Create a mask for the bits under bit i
    #[inline(always)]
    fn mask_higher(i: u8) -> [u128; 2] {
        [
            u128::MAX.checked_shl(1 + i as u32).unwrap_or_default(),
            u128::MAX
                .checked_shl(i.saturating_sub(127) as u32)
                .unwrap_or_default(),
        ]
    }

    pub(crate) fn is_present(&self, k: u8) -> bool {
        self.0[k as usize / 128] & (1 << (k % 128)) != 0
    }
    pub(crate) fn set_bit(&mut self, k: u8) {
        Self::array_set_bit(&mut self.0, k);
    }
    pub(crate) fn array_set_bit(a: &mut [u128; 2], k: u8) {
        a[k as usize / 128] |= 1 << (k % 128);
    }
    pub(crate) fn unset_bit(&mut self, k: u8) {
        self.0[k as usize / 128] &= !(1 << (k % 128));
    }
}

impl BitAndAssign<ByteSet> for [u128; 2] {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: ByteSet) {
        self[0] &= rhs.0[0];
        self[1] &= rhs.0[1];
    }
}

impl VebTree for ByteSet {
    type Key = u8;
    type Value = ();

    fn from_monad(k: Self::Key, v: Self::Value) -> Self {
        let mut a = [0; 2];
        Self::array_set_bit(&mut a, k);
        Self(a, v)
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
    fn min_val(&self) -> (MaybeBorrowed<Self::Key>, &Self::Value) {
        (MaybeBorrowed::Owned(self.lowest()), &self.1)
    }
    fn min_val_mut(&mut self) -> (MaybeBorrowed<Self::Key>, &mut Self::Value) {
        (MaybeBorrowed::Owned(self.lowest()), &mut self.1)
    }
    fn max_val(&self) -> (MaybeBorrowed<Self::Key>, &Self::Value) {
        (MaybeBorrowed::Owned(self.highest()), &self.1)
    }
    fn max_val_mut(&mut self) -> (MaybeBorrowed<Self::Key>, &mut Self::Value) {
        (MaybeBorrowed::Owned(self.highest()), &mut self.1)
    }

    fn find<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = k.into().into_or_clone();
        if self.is_present(k) {
            Some((MaybeBorrowed::Owned(k), &self.1))
        } else {
            None
        }
    }
    fn find_mut<'a, Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = k.into().into_or_clone();
        if self.is_present(k) {
            Some((MaybeBorrowed::Owned(k), &mut self.1))
        } else {
            None
        }
    }

    fn predecessor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let mut k = Self::mask_lower(k.into().into_or_clone());
        k &= *self;
        Self::from_array(k).map(|v| (MaybeBorrowed::Owned(v.highest()), &self.1))
    }
    fn predecessor_mut<'a, Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let mut k = Self::mask_lower(k.into().into_or_clone());
        k &= *self;
        Self::from_array(k).map(|v| (MaybeBorrowed::Owned(v.highest()), &mut self.1))
    }
    fn successor<'a, Q>(&self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let mut k = Self::mask_higher(k.into().into_or_clone());
        k &= *self;
        Self::from_array(k).map(|v| (MaybeBorrowed::Owned(v.lowest()), &self.1))
    }
    fn successor_mut<'a, Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<Self::Key>, &mut Self::Value)>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let mut k = Self::mask_higher(k.into().into_or_clone());
        k &= *self;
        Self::from_array(k).map(|v| (MaybeBorrowed::Owned(v.lowest()), &mut self.1))
    }
    fn insert(&mut self, k: u8, v: Self::Value) -> Option<(Self::Key, Self::Value)> {
        if self.is_present(k) {
            Some((k, v))
        } else {
            self.set_bit(k);
            None
        }
    }

    fn remove<'a, Q>(mut self, k: Q) -> MaybeRemoveResult<Self>
    where
        Q: Into<MaybeBorrowed<'a, Self::Key>>,
        Self::Key: 'a,
    {
        let k = k.into().into_or_clone();
        if !self.is_present(k) {
            Err(self)
        } else if self.len() == 1 {
            Ok((None, (k, ())))
        } else {
            self.unset_bit(k);
            Ok((Some(self), (k, ())))
        }
    }
    fn remove_min(mut self) -> (Option<Self>, (Self::Key, Self::Value)) {
        let k = self.lowest();
        if self.len() == 1 {
            (None, (k, ()))
        } else {
            self.unset_bit(k);
            (Some(self), (k, ()))
        }
    }
    fn remove_max(mut self) -> (Option<Self>, (Self::Key, Self::Value)) {
        let k = self.highest();
        if self.len() == 1 {
            return (None, (k, ()));
        } else {
            self.unset_bit(k);
            (Some(self), (k, ()))
        }
    }
}

#[cfg(test)]
mod test {
    use super::ByteSet;
    use crate::{key::MaybeBorrowed, VebTree};
    #[test]
    fn test_masks() {
        for i in 0usize..128 {
            let r = [(1 << i) - 1, 0];
            assert_eq!(ByteSet::mask_lower(i as u8), r, "{i}");
        }
        for i in 0usize..127 {
            let r = [u128::MAX, (1 << i) - 1];
            assert_eq!(ByteSet::mask_lower(128 + i as u8), r, "{i}");
        }
        for i in 0..=255 {
            let mut mask = ByteSet::mask_lower(i);
            mask &= ByteSet::from_monad(i, ());
            assert_eq!(mask, [0, 0])
        }
    }

    #[test]
    fn simple_set() {
        let mut set = ByteSet::from_monad(0, ());
        for i in 1..=255u8 {
            assert_eq!(set.lowest(), 0);
            assert_eq!(set.highest(), i - 1);
            assert_eq!(set.predecessor(i), Some((MaybeBorrowed::Owned(i - 1), &())));
            set.insert(i, ());
            assert_eq!(set.successor(0), Some((MaybeBorrowed::Owned(1), &())));
            assert_eq!(set.successor(i - 1), Some((MaybeBorrowed::Owned(i), &())));
            assert_eq!(set.predecessor(i), Some((MaybeBorrowed::Owned(i - 1), &())));
        }
        assert_eq!(set.highest(), 255);

        let mut set = ByteSet::from_monad(0, ());
        for i in 1..=255u8 {
            assert_eq!(set.successor(i - 1), None);
            assert_eq!(set.lowest(), i - 1);
            assert_eq!(set.highest(), i - 1);
            assert_eq!(set.predecessor(i - 1), None);
            assert_eq!(set.predecessor(i), Some((MaybeBorrowed::Owned(i - 1), &())));
            set.insert(i, ());
            if i > 1 {
                assert_eq!(set.successor(0), Some((MaybeBorrowed::Owned(i - 1), &())));
            }
            assert_eq!(set.successor(i - 1), Some((MaybeBorrowed::Owned(i), &())));
            assert_eq!(set.highest(), i);
            let v = set.remove(i - 1).unwrap();
            set = v.0.unwrap();
            assert_eq!(v.1, ((i - 1), ()));
            assert_eq!(set.successor(0), Some((MaybeBorrowed::Owned(i), &())));
        }
        assert_eq!(set.lowest(), 255);
        assert_eq!(set.highest(), 255);
    }
}
