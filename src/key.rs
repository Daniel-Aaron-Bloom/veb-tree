use core::{
    borrow::Borrow,
    ops::Deref,
    ops::{BitOr, Shl, Shr},
};

use typenum::{op, Unsigned, U1, U128, U16, U2 as _U2, U32, U4 as _U4, U64, U8};

#[derive(Clone, Copy, Debug, Eq)]
pub enum MaybeBorrowed<'a, B> {
    Borrowed(&'a B),
    Owned(B),
}

impl<'l, 'r, L, R> PartialEq<MaybeBorrowed<'r, R>> for MaybeBorrowed<'l, L>
where
    L: PartialEq<R>,
{
    #[inline(always)]
    fn eq(&self, other: &MaybeBorrowed<'r, R>) -> bool {
        **self == **other
    }
}

impl<'a, B> From<B> for MaybeBorrowed<'a, B> {
    #[inline(always)]
    fn from(b: B) -> Self {
        Self::Owned(b)
    }
}
impl<'a, B> From<&'a B> for MaybeBorrowed<'a, B> {
    #[inline(always)]
    fn from(b: &'a B) -> Self {
        Self::Borrowed(b)
    }
}

impl<'a, B: Clone> MaybeBorrowed<'a, B> {
    #[inline(always)]
    pub fn into_or_clone(self) -> B {
        match self {
            Self::Borrowed(b) => b.clone(),
            Self::Owned(b) => b,
        }
    }
}
impl<'a, B> MaybeBorrowed<'a, B> {
    #[inline(always)]
    pub fn borrow(&'a self) -> Self {
        Self::Borrowed(self)
    }
}

impl<'a, B> Borrow<B> for MaybeBorrowed<'a, B> {
    #[inline(always)]
    fn borrow(&self) -> &B {
        self
    }
}

impl<'a, B> Deref for MaybeBorrowed<'a, B> {
    type Target = B;
    #[inline(always)]
    fn deref(&self) -> &B {
        match self {
            Self::Borrowed(b) => b,
            Self::Owned(ref b) => b,
        }
    }
}

/// A trait to enable splitting and recombining keys into a `Hi` and `Lo` component.
///
/// A given value must ensure that values are split and recombined correctly, and that
/// sort order is preserved, i.e. `self.cmp(rhs) == (self.hi, self.lo).cmp((rhs.hi, rhs.lo))`
pub trait VebKey: Ord {
    type Hi: Ord;
    type Lo: Ord;

    fn split_val(self) -> (Self::Hi, Self::Lo);
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self;
}

pub trait VebKeyRef<Hi: Ord, Lo: Ord> {
    fn split_ref<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&Hi, &Lo) -> R;
}

trait CloneVebKeyRef: VebKey + Clone + Ord {}

impl<T: CloneVebKeyRef> VebKeyRef<T::Hi, T::Lo> for T {
    #[inline(always)]
    fn split_ref<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T::Hi, &T::Lo) -> R,
    {
        let (hi, lo) = self.clone().split_val();
        f(&hi, &lo)
    }
}

pub trait SizedVebKey {
    const CARDINALITY: usize;
    type Cardinality: Unsigned;
    fn index(&self) -> usize;
}

impl VebKey for () {
    type Hi = ();
    type Lo = ();
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        ((), ())
    }
    #[inline(always)]
    fn join<'a>(_hi: MaybeBorrowed<'a, Self::Hi>, _lo: MaybeBorrowed<'a, Self::Lo>) -> Self {}
}
impl CloneVebKeyRef for () {}
impl SizedVebKey for () {
    const CARDINALITY: usize = 1;
    type Cardinality = typenum::U1;
    fn index(&self) -> usize {
        0
    }
}

impl VebKey for u128 {
    type Hi = u64;
    type Lo = u64;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        ((self >> Self::Lo::BITS) as Self::Hi, (self as Self::Lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let (hi, lo) = (hi.into_or_clone() as Self, lo.into_or_clone() as Self);
        hi << 64 | lo
    }
}
impl CloneVebKeyRef for u128 {}
impl SizedVebKey for u128 {
    const CARDINALITY: usize = if usize::MAX as Self >= Self::MAX {
        u128::MAX as usize
    } else {
        panic!("u128 is not sized on this platform")
    };
    type Cardinality = op!(U1 << U128);
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}

impl VebKey for i128 {
    type Hi = u64;
    type Lo = u64;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        self.abs_diff(Self::MIN).split_val()
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        (u128::join(hi, lo) as Self).wrapping_add(Self::MIN)
    }
}
impl CloneVebKeyRef for i128 {}
impl SizedVebKey for i128 {
    const CARDINALITY: usize = if usize::MAX as u128 >= u128::MAX {
        u128::MAX as usize
    } else {
        panic!("i128 is not sized on this platform")
    };
    type Cardinality = op!(U1 << U128);
    #[inline(always)]
    fn index(&self) -> usize {
        self.wrapping_sub(Self::MIN) as usize
    }
}

impl VebKey for u64 {
    type Hi = u32;
    type Lo = u32;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        ((self >> Self::Lo::BITS) as Self::Hi, (self as Self::Lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let (hi, lo) = (hi.into_or_clone() as Self, lo.into_or_clone() as Self);
        hi << 32 | lo
    }
}
impl CloneVebKeyRef for u64 {}
impl SizedVebKey for u64 {
    const CARDINALITY: usize = if usize::MAX as Self >= Self::MAX {
        Self::MAX as usize
    } else {
        panic!("u64 is not sized on this platform")
    };
    type Cardinality = op!(U1 << U64);
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}

impl VebKey for i64 {
    type Hi = u32;
    type Lo = u32;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        self.abs_diff(Self::MIN).split_val()
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        (u64::join(hi, lo) as Self).wrapping_add(Self::MIN)
    }
}
impl CloneVebKeyRef for i64 {}
impl SizedVebKey for i64 {
    const CARDINALITY: usize = if usize::MAX as u64 >= u64::MAX {
        u64::MAX as usize
    } else {
        panic!("i64 is not sized on this platform")
    };
    type Cardinality = op!(U1 << U64);
    #[inline(always)]
    fn index(&self) -> usize {
        self.wrapping_sub(Self::MIN) as usize
    }
}

impl VebKey for u32 {
    type Hi = u16;
    type Lo = u16;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        ((self >> Self::Lo::BITS) as Self::Hi, (self as Self::Lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let (hi, lo) = (hi.into_or_clone() as Self, lo.into_or_clone() as u32);
        hi << 16 | lo
    }
}
impl CloneVebKeyRef for u32 {}
impl SizedVebKey for u32 {
    const CARDINALITY: usize = if usize::MAX as Self >= Self::MAX {
        Self::MAX as usize
    } else {
        panic!("u32 is not sized on this platform")
    };
    type Cardinality = op!(U1 << U32);
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}

impl VebKey for i32 {
    type Hi = u16;
    type Lo = u16;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        self.abs_diff(Self::MIN).split_val()
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        (u32::join(hi, lo) as Self).wrapping_add(Self::MIN)
    }
}
impl CloneVebKeyRef for i32 {}
impl SizedVebKey for i32 {
    const CARDINALITY: usize = if usize::MAX as u32 >= u32::MAX {
        u32::MAX as usize
    } else {
        panic!("i32 is not sized on this platform")
    };
    type Cardinality = op!(U1 << U32);
    #[inline(always)]
    fn index(&self) -> usize {
        self.wrapping_sub(Self::MIN) as usize
    }
}

impl VebKey for u16 {
    type Hi = u8;
    type Lo = u8;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        ((self >> Self::Lo::BITS) as Self::Hi, (self as Self::Lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let (hi, lo) = (hi.into_or_clone() as Self, lo.into_or_clone() as Self);
        hi << 8 | lo
    }
}
impl CloneVebKeyRef for u16 {}
impl SizedVebKey for u16 {
    const CARDINALITY: usize = if usize::MAX as Self >= Self::MAX {
        Self::MAX as usize
    } else {
        panic!("u16 is not sized on this platform")
    };
    type Cardinality = op!(U1 << U16);
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}

impl VebKey for i16 {
    type Hi = u8;
    type Lo = u8;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        self.abs_diff(Self::MIN).split_val()
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        (u16::join(hi, lo) as Self).wrapping_add(Self::MIN)
    }
}
impl CloneVebKeyRef for i16 {}
impl SizedVebKey for i16 {
    const CARDINALITY: usize = if usize::MAX as u16 >= u16::MAX {
        u16::MAX as usize
    } else {
        panic!("i16 is not sized on this platform")
    };
    type Cardinality = op!(U1 << U16);
    #[inline(always)]
    fn index(&self) -> usize {
        self.wrapping_sub(Self::MIN) as usize
    }
}

impl VebKey for u8 {
    type Hi = U4;
    type Lo = U4;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        (Self::Hi::new(self >> Self::Lo::BITS), Self::Lo::from(self))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let (hi, lo) = (hi.into_or_clone().0, lo.into_or_clone().0);
        hi << 4 | lo
    }
}
impl CloneVebKeyRef for u8 {}
impl SizedVebKey for u8 {
    const CARDINALITY: usize = if usize::MAX as u8 >= u8::MAX {
        u8::MAX as usize
    } else {
        panic!("u8 is not sized on this platform")
    };
    type Cardinality = op!(U1 << U8);
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}

impl VebKey for i8 {
    type Hi = U4;
    type Lo = U4;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        self.abs_diff(Self::MIN).split_val()
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        (u8::join(hi, lo) as Self).wrapping_add(Self::MIN)
    }
}
impl CloneVebKeyRef for i8 {}
impl SizedVebKey for i8 {
    const CARDINALITY: usize = if usize::MAX as u8 >= u8::MAX {
        u8::MAX as usize
    } else {
        panic!("i8 is not sized on this platform")
    };
    type Cardinality = op!(U1 << U8);
    #[inline(always)]
    fn index(&self) -> usize {
        self.wrapping_sub(Self::MIN) as usize
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct U4(u8);

impl U4 {
    pub const BITS: u32 = 4;
    pub const MAX: u8 = u8::MAX >> (u8::BITS - Self::BITS);
    const fn new(v: u8) -> Self {
        Self(v)
    }
}

impl From<u8> for U4 {
    fn from(value: u8) -> Self {
        Self(value & Self::MAX)
    }
}
impl From<U4> for u8 {
    fn from(value: U4) -> Self {
        value.0
    }
}

impl BitOr for U4 {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self::from(self.0 | rhs.0)
    }
}

impl Shl<usize> for U4 {
    type Output = Self;
    fn shl(self, rhs: usize) -> Self::Output {
        Self::from(self.0.shl(rhs))
    }
}

impl Shr<usize> for U4 {
    type Output = Self;
    fn shr(self, rhs: usize) -> Self::Output {
        Self::from(self.0.shr(rhs))
    }
}

impl VebKey for U4 {
    type Hi = U2;
    type Lo = U2;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        (
            Self::Hi::new(self.0 >> Self::Lo::BITS),
            Self::Lo::from(self),
        )
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let (hi, lo) = (hi.into_or_clone().0, lo.into_or_clone().0);
        Self(hi << 2 | lo)
    }
}
impl CloneVebKeyRef for U4 {}
impl SizedVebKey for U4 {
    const CARDINALITY: usize = Self::MAX as usize;
    type Cardinality = op!(U1 << _U4);
    #[inline(always)]
    fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct U2(u8);

impl U2 {
    pub const BITS: u32 = 2;
    pub const MAX: u8 = u8::MAX >> (u8::BITS - Self::BITS);
    const fn new(v: u8) -> Self {
        Self(v)
    }
}
impl From<u8> for U2 {
    fn from(value: u8) -> Self {
        Self(value & Self::MAX)
    }
}
impl From<U4> for U2 {
    fn from(value: U4) -> Self {
        Self::from(value.0)
    }
}
impl From<U2> for U4 {
    fn from(value: U2) -> Self {
        Self(value.0)
    }
}
impl From<U2> for bool {
    fn from(value: U2) -> Self {
        value.0 & 1 == 1
    }
}

impl BitOr for U2 {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self::from(self.0 | rhs.0)
    }
}

impl Shl<usize> for U2 {
    type Output = Self;
    fn shl(self, rhs: usize) -> Self::Output {
        Self::from(self.0.shl(rhs))
    }
}

impl Shr<usize> for U2 {
    type Output = Self;
    fn shr(self, rhs: usize) -> Self::Output {
        Self::from(self.0.shr(rhs))
    }
}

impl VebKey for U2 {
    type Hi = bool;
    type Lo = bool;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        (self.0 >> 1 != 0, Self::Lo::from(self))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let (hi, lo) = (hi.into_or_clone() as u8, lo.into_or_clone() as u8);
        Self(hi << 1 | lo)
    }
}
impl CloneVebKeyRef for U2 {}
impl SizedVebKey for U2 {
    const CARDINALITY: usize = Self::MAX as usize;
    type Cardinality = op!(U1 << _U2);
    #[inline(always)]
    fn index(&self) -> usize {
        self.0 as usize
    }
}

impl<T: Clone + Ord> VebKey for [T; 2] {
    type Hi = T;
    type Lo = T;
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        let [hi, lo] = self;
        (hi, lo)
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        [hi.into_or_clone(), lo.into_or_clone()]
    }
}
impl<T: Ord> VebKeyRef<T, T> for [T; 2] {
    #[inline(always)]
    fn split_ref<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T, &T) -> R,
    {
        f(&self[0], &self[1])
    }
}

impl<T: Clone + Ord> VebKey for [T; 3] {
    type Hi = T;
    type Lo = [T; 2];
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        let [hi, lo @ ..] = self;
        (hi, lo)
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let (hi, [lo0, lo1]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi, lo0, lo1]
    }
}
impl<T: Ord> VebKeyRef<T, [T; 2]> for [T; 3] {
    #[inline(always)]
    fn split_ref<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T, &[T; 2]) -> R,
    {
        let [hi, lo @ ..] = self;
        f(hi, lo)
    }
}
impl<T: Clone + Ord> VebKey for [T; 4] {
    type Hi = [T; 2];
    type Lo = [T; 2];
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        let [h0, h1, lo @ ..] = self;
        ([h0, h1], lo)
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let ([hi0, hi1], [lo0, lo1]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi0, hi1, lo0, lo1]
    }
}
impl<T: Ord> VebKeyRef<[T; 2], [T; 2]> for [T; 4] {
    #[inline(always)]
    fn split_ref<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&[T; 2], &[T; 2]) -> R,
    {
        let [hi @ .., _, _] = self;
        let [_, _, lo @ ..] = self;
        f(hi, lo)
    }
}
impl<T: Clone + Ord> VebKey for [T; 5] {
    type Hi = [T; 2];
    type Lo = [T; 3];
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        let [h0, h1, lo @ ..] = self;
        ([h0, h1], lo)
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let ([hi0, hi1], [lo0, lo1, lo2]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi0, hi1, lo0, lo1, lo2]
    }
}
impl<T: Ord> VebKeyRef<[T; 2], [T; 3]> for [T; 5] {
    #[inline(always)]
    fn split_ref<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&[T; 2], &[T; 3]) -> R,
    {
        let [hi @ .., _, _, _] = self;
        let [_, _, lo @ ..] = self;
        f(hi, lo)
    }
}
impl<T: Clone + Ord> VebKey for [T; 6] {
    type Hi = [T; 3];
    type Lo = [T; 3];
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        let [h0, h1, h2, lo @ ..] = self;
        ([h0, h1, h2], lo)
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let ([hi0, hi1, hi2], [lo0, lo1, lo2]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi0, hi1, hi2, lo0, lo1, lo2]
    }
}
impl<T: Ord> VebKeyRef<[T; 3], [T; 3]> for [T; 6] {
    #[inline(always)]
    fn split_ref<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&[T; 3], &[T; 3]) -> R,
    {
        let [hi @ .., _, _, _] = self;
        let [_, _, _, lo @ ..] = self;
        f(hi, lo)
    }
}
impl<T: Clone + Ord> VebKey for [T; 7] {
    type Hi = [T; 3];
    type Lo = [T; 4];
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        let [h0, h1, h2, lo @ ..] = self;
        ([h0, h1, h2], lo)
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let ([hi0, hi1, hi2], [lo0, lo1, lo2, lo3]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi0, hi1, hi2, lo0, lo1, lo2, lo3]
    }
}
impl<T: Ord> VebKeyRef<[T; 3], [T; 4]> for [T; 7] {
    #[inline(always)]
    fn split_ref<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&[T; 3], &[T; 4]) -> R,
    {
        let [hi @ .., _, _, _, _] = self;
        let [_, _, _, lo @ ..] = self;
        f(hi, lo)
    }
}
impl<T: Clone + Ord> VebKey for [T; 8] {
    type Hi = [T; 4];
    type Lo = [T; 4];
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        let [h0, h1, h2, h3, lo @ ..] = self;
        ([h0, h1, h2, h3], lo)
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let ([hi0, hi1, hi2, hi3], [lo0, lo1, lo2, lo3]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi0, hi1, hi2, hi3, lo0, lo1, lo2, lo3]
    }
}
impl<T: Ord> VebKeyRef<[T; 4], [T; 4]> for [T; 8] {
    #[inline(always)]
    fn split_ref<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&[T; 4], &[T; 4]) -> R,
    {
        let [hi @ .., _, _, _, _] = self;
        let [_, _, _, _, lo @ ..] = self;
        f(hi, lo)
    }
}
impl<T: Clone + Ord> VebKey for [T; 16] {
    type Hi = [T; 8];
    type Lo = [T; 8];
    #[inline(always)]
    fn split_val(self) -> (Self::Hi, Self::Lo) {
        let [h0, h1, h2, h3, h4, h5, h6, h7, lo @ ..] = self;
        ([h0, h1, h2, h3, h4, h5, h6, h7], lo)
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::Hi>, lo: MaybeBorrowed<'a, Self::Lo>) -> Self {
        let ([hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7], [lo0, lo1, lo2, lo3, lo4, lo5, lo6, lo7]) =
            (hi.into_or_clone(), lo.into_or_clone());
        [
            hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, lo0, lo1, lo2, lo3, lo4, lo5, lo6, lo7,
        ]
    }
}
impl<T: Ord> VebKeyRef<[T; 8], [T; 8]> for [T; 16] {
    #[inline(always)]
    fn split_ref<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&[T; 8], &[T; 8]) -> R,
    {
        let [hi @ .., _, _, _, _, _, _, _, _] = self;
        let [_, _, _, _, _, _, _, _, lo @ ..] = self;
        f(hi, lo)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn signed_i8_ordering() {
        // Test all i8 values (only 256 values, fast enough)
        for lhs in i8::MIN..=i8::MAX {
            let (lh, ll) = lhs.split_val();
            for rhs in i8::MIN..=i8::MAX {
                let (rh, rl) = rhs.split_val();
                assert_eq!(
                    lhs.cmp(&rhs),
                    (lh, ll).cmp(&(rh, rl)),
                    "Failed for lhs={lhs}, rhs={rhs}"
                );
            }
        }
    }

    #[test]
    fn signed_i16_ordering_sample() {
        // Test a representative sample of i16 values
        let test_values = [
            i16::MIN,
            i16::MIN + 1,
            -1000,
            -100,
            -1,
            0,
            1,
            100,
            1000,
            i16::MAX - 1,
            i16::MAX,
        ];

        for &lhs in &test_values {
            let (lh, ll) = lhs.split_val();
            for &rhs in &test_values {
                let (rh, rl) = rhs.split_val();
                assert_eq!(
                    lhs.cmp(&rhs),
                    (lh, ll).cmp(&(rh, rl)),
                    "Failed for lhs={lhs}, rhs={rhs}"
                );
            }
        }
    }

    #[test]
    fn signed_i32_ordering_sample() {
        let test_values = [
            i32::MIN,
            i32::MIN + 1,
            -1000000,
            -1000,
            -1,
            0,
            1,
            1000,
            1000000,
            i32::MAX - 1,
            i32::MAX,
        ];

        for &lhs in &test_values {
            let (lh, ll) = lhs.split_val();
            for &rhs in &test_values {
                let (rh, rl) = rhs.split_val();
                assert_eq!(
                    lhs.cmp(&rhs),
                    (lh, ll).cmp(&(rh, rl)),
                    "Failed for lhs={lhs}, rhs={rhs}"
                );
            }
        }
    }

    #[test]
    fn signed_split_join_roundtrip() {
        // Test split/join roundtrip for various signed types
        let i8_values = [i8::MIN, -1, 0, 1, i8::MAX];
        for &val in &i8_values {
            let (hi, lo) = val.split_val();
            let reconstructed = i8::join(hi.into(), lo.into());
            assert_eq!(val, reconstructed, "i8 roundtrip failed for {val}");
        }

        let i16_values = [i16::MIN, -1000, -1, 0, 1, 1000, i16::MAX];
        for &val in &i16_values {
            let (hi, lo) = val.split_val();
            let reconstructed = i16::join(hi.into(), lo.into());
            assert_eq!(val, reconstructed, "i16 roundtrip failed for {val}");
        }

        let i32_values = [i32::MIN, -1000000, -1, 0, 1, 1000000, i32::MAX];
        for &val in &i32_values {
            let (hi, lo) = val.split_val();
            let reconstructed = i32::join(hi.into(), lo.into());
            assert_eq!(val, reconstructed, "i32 roundtrip failed for {val}");
        }

        let i64_values = [i64::MIN, -1000000000, -1, 0, 1, 1000000000, i64::MAX];
        for &val in &i64_values {
            let (hi, lo) = val.split_val();
            let reconstructed = i64::join(hi.into(), lo.into());
            assert_eq!(val, reconstructed, "i64 roundtrip failed for {val}");
        }
    }

    #[test]
    fn u2_bool_conversion() {
        // Test all 4 possible U2 values
        assert_eq!(
            bool::from(U2::from(0u8)),
            false,
            "U2(0) should convert to false"
        );
        assert_eq!(
            bool::from(U2::from(1u8)),
            true,
            "U2(1) should convert to true"
        );
        assert_eq!(
            bool::from(U2::from(2u8)),
            false,
            "U2(2) should convert to false"
        );
        assert_eq!(
            bool::from(U2::from(3u8)),
            true,
            "U2(3) should convert to true"
        );
    }

    #[test]
    fn u2_split_join_roundtrip() {
        for i in 0..=3u8 {
            let u2_val = U2::from(i);
            let (hi, lo) = u2_val.split_val();
            let reconstructed = U2::join(hi.into(), lo.into());
            assert_eq!(u2_val, reconstructed, "U2 roundtrip failed for {i}");
        }
    }

    #[test]
    fn u4_split_join_roundtrip() {
        for i in 0..=15u8 {
            let u4_val = U4::from(i);
            let (hi, lo) = u4_val.split_val();
            let reconstructed = U4::join(hi.into(), lo.into());
            assert_eq!(u4_val, reconstructed, "U4 roundtrip failed for {i}");
        }
    }

    #[test]
    fn unsigned_split_join_roundtrip() {
        // Test u8
        for val in 0..=255u8 {
            let (hi, lo) = val.split_val();
            let reconstructed = u8::join(hi.into(), lo.into());
            assert_eq!(val, reconstructed, "u8 roundtrip failed for {val}");
        }

        // Test sample of larger types
        let u16_values = [0u16, 1, 255, 256, 1000, u16::MAX - 1, u16::MAX];
        for &val in &u16_values {
            let (hi, lo) = val.split_val();
            let reconstructed = u16::join(hi.into(), lo.into());
            assert_eq!(val, reconstructed, "u16 roundtrip failed for {val}");
        }

        let u32_values = [0u32, 1, 65535, 65536, 1000000, u32::MAX - 1, u32::MAX];
        for &val in &u32_values {
            let (hi, lo) = val.split_val();
            let reconstructed = u32::join(hi.into(), lo.into());
            assert_eq!(val, reconstructed, "u32 roundtrip failed for {val}");
        }

        let u64_values = [0u64, 1, 0xFFFFFFFF, 0x100000000, u64::MAX - 1, u64::MAX];
        for &val in &u64_values {
            let (hi, lo) = val.split_val();
            let reconstructed = u64::join(hi.into(), lo.into());
            assert_eq!(val, reconstructed, "u64 roundtrip failed for {val}");
        }
    }

    #[test]
    fn array_key_split_join_roundtrip() {
        // Test [T; 2]
        let arr2 = [5u8, 10u8];
        let (hi, lo) = arr2.split_val();
        let reconstructed = <[u8; 2]>::join(hi.into(), lo.into());
        assert_eq!(arr2, reconstructed, "[u8; 2] roundtrip failed");

        // Test [T; 3]
        let arr3 = [5u8, 10u8, 15u8];
        let (hi, lo) = arr3.split_val();
        let reconstructed = <[u8; 3]>::join(hi.into(), lo.into());
        assert_eq!(arr3, reconstructed, "[u8; 3] roundtrip failed");

        // Test [T; 4]
        let arr4 = [1u8, 2u8, 3u8, 4u8];
        let (hi, lo) = arr4.split_val();
        let reconstructed = <[u8; 4]>::join(hi.into(), lo.into());
        assert_eq!(arr4, reconstructed, "[u8; 4] roundtrip failed");

        // Test [T; 8]
        let arr8 = [1u8, 2, 3, 4, 5, 6, 7, 8];
        let (hi, lo) = arr8.split_val();
        let reconstructed = <[u8; 8]>::join(hi.into(), lo.into());
        assert_eq!(arr8, reconstructed, "[u8; 8] roundtrip failed");
    }

    #[test]
    fn array_key_ordering_preserved() {
        // Test that array ordering matches tuple ordering
        let arr1 = [1u8, 5u8];
        let arr2 = [1u8, 10u8];
        let arr3 = [2u8, 3u8];

        let (h1, l1) = arr1.split_val();
        let (h2, l2) = arr2.split_val();
        let (h3, l3) = arr3.split_val();

        assert_eq!(arr1.cmp(&arr2), (&h1, &l1).cmp(&(&h2, &l2)));
        assert_eq!(arr1.cmp(&arr3), (&h1, &l1).cmp(&(&h3, &l3)));
        assert_eq!(arr2.cmp(&arr3), (&h2, &l2).cmp(&(&h3, &l3)));
    }

    #[test]
    #[ignore] // Very slow test - only run when needed
    fn signed_i16_complete_ordering() {
        for lhs in i16::MIN..=i16::MAX {
            let (lh, ll) = lhs.split_val();
            for rhs in i16::MIN..=i16::MAX {
                let (rh, rl) = rhs.split_val();
                assert_eq!(lhs.cmp(&rhs), (lh, ll).cmp(&(rh, rl)));
            }
        }
    }
}
