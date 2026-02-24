use core::{borrow::Borrow, ops::BitAndAssign};

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

    /// Create a mask with all bits set that are strictly greater than bit i.
    ///
    /// Returns a 256-bit mask (as [u128; 2]) where bits at positions > i are set to 1,
    /// and all other bits (including bit i itself) are set to 0.
    #[inline(always)]
    fn mask_higher(i: u8) -> [u128; 2] {
        [
            u128::MAX.checked_shl(1 + i as u32).unwrap_or_default(),
            u128::MAX
                .checked_shl(i.saturating_sub(127) as u32)
                .unwrap_or_default(),
        ]
    }

    #[inline(always)]
    pub(crate) fn is_present(&self, k: u8) -> bool {
        self.0[k as usize / 128] & (1 << (k % 128)) != 0
    }
    #[inline(always)]
    pub(crate) fn set_bit(&mut self, k: u8) {
        Self::array_set_bit(&mut self.0, k);
    }
    #[inline(always)]
    pub(crate) fn array_set_bit(a: &mut [u128; 2], k: u8) {
        a[k as usize / 128] |= 1 << (k % 128);
    }
    #[inline(always)]
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
    #[inline(always)]
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
    fn min_val(&self) -> (MaybeBorrowed<'_, Self::Key>, &Self::Value) {
        (MaybeBorrowed::Owned(self.lowest()), &self.1)
    }
    fn min_val_mut(&mut self) -> (MaybeBorrowed<'_, Self::Key>, &mut Self::Value) {
        (MaybeBorrowed::Owned(self.lowest()), &mut self.1)
    }
    fn max_val(&self) -> (MaybeBorrowed<'_, Self::Key>, &Self::Value) {
        (MaybeBorrowed::Owned(self.highest()), &self.1)
    }
    fn max_val_mut(&mut self) -> (MaybeBorrowed<'_, Self::Key>, &mut Self::Value) {
        (MaybeBorrowed::Owned(self.highest()), &mut self.1)
    }

    fn find<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        let k = *k.borrow();
        if self.is_present(k) {
            Some((MaybeBorrowed::Owned(k), &self.1))
        } else {
            None
        }
    }
    fn find_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        let k = *k.borrow();
        if self.is_present(k) {
            Some((MaybeBorrowed::Owned(k), &mut self.1))
        } else {
            None
        }
    }

    fn predecessor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        let mut k = Self::mask_lower(*k.borrow());
        k &= *self;
        Self::from_array(k).map(|v| (MaybeBorrowed::Owned(v.highest()), &self.1))
    }
    fn predecessor_mut<Q>(
        &mut self,
        k: Q,
    ) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        let mut k = Self::mask_lower(*k.borrow());
        k &= *self;
        Self::from_array(k).map(|v| (MaybeBorrowed::Owned(v.highest()), &mut self.1))
    }
    fn successor<Q>(&self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        let mut k = Self::mask_higher(*k.borrow());
        k &= *self;
        Self::from_array(k).map(|v| (MaybeBorrowed::Owned(v.lowest()), &self.1))
    }
    fn successor_mut<Q>(&mut self, k: Q) -> Option<(MaybeBorrowed<'_, Self::Key>, &mut Self::Value)>
    where
        Q: Borrow<Self::Key>,
    {
        let mut k = Self::mask_higher(*k.borrow());
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

    fn remove<Q>(mut self, k: Q) -> MaybeRemoveResult<Self>
    where
        Q: Borrow<Self::Key>,
    {
        let k = *k.borrow();
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
            (None, (k, ()))
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
    fn test_mask_higher() {
        // Test boundary case: i=0 should have all bits 1-255 set
        assert_eq!(ByteSet::mask_higher(0), [u128::MAX << 1, u128::MAX]);

        // Test boundary case: i=255 should have no bits set
        assert_eq!(ByteSet::mask_higher(255), [0, 0]);

        // Test first u128 range (bits 0-126)
        for i in 0usize..127 {
            let expected_first = u128::MAX.checked_shl(1 + i as u32).unwrap();
            let expected_second = u128::MAX;
            assert_eq!(
                ByteSet::mask_higher(i as u8),
                [expected_first, expected_second],
                "Failed for i={i}"
            );
        }

        // Test boundary between u128s: i=127
        assert_eq!(ByteSet::mask_higher(127), [0, u128::MAX]);

        // Test second u128 range (bits 128-254)
        for i in 128usize..255 {
            let expected_first = 0u128;
            let expected_second = u128::MAX.checked_shl((i - 127) as u32).unwrap();
            assert_eq!(
                ByteSet::mask_higher(i as u8),
                [expected_first, expected_second],
                "Failed for i={i}"
            );
        }

        // Verify that bit i itself is never included in the mask
        for i in 0..=255 {
            let mut mask = ByteSet::mask_higher(i);
            mask &= ByteSet::from_monad(i, ());
            assert_eq!(mask, [0, 0], "Bit {i} should not be in its own higher mask");
        }

        // Verify that mask_lower(i), bit i, and mask_higher(i) partition all bits
        for i in 0..=255 {
            let lower = ByteSet::mask_lower(i);
            let higher = ByteSet::mask_higher(i);
            let bit_i = ByteSet::from_monad(i, ()).0;

            // Together they should cover all bits
            let combined = [
                lower[0] | bit_i[0] | higher[0],
                lower[1] | bit_i[1] | higher[1],
            ];
            assert_eq!(
                combined,
                [u128::MAX, u128::MAX],
                "Failed to partition all bits at i={i}"
            );

            // They should not overlap
            assert_eq!(
                [lower[0] & higher[0], lower[1] & higher[1]],
                [0, 0],
                "lower and higher masks overlap at i={i}"
            );
            assert_eq!(
                [lower[0] & bit_i[0], lower[1] & bit_i[1]],
                [0, 0],
                "lower mask includes bit i at i={i}"
            );
            assert_eq!(
                [higher[0] & bit_i[0], higher[1] & bit_i[1]],
                [0, 0],
                "higher mask includes bit i at i={i}"
            );
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
