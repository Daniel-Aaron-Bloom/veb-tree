use core::{
    borrow::Borrow,
    ops::Deref,
    ops::{BitOr, Shl, Shr},
};

pub struct Owned<T>(pub T);

impl<T> From<T> for Owned<T> {
    fn from(t: T) -> Self {
        Owned(t)
    }
}

impl<'a, T: Clone> From<&'a T> for Owned<T> {
    fn from(t: &'a T) -> Self {
        Owned(t.clone())
    }
}

impl<'a, T: Clone> From<MaybeBorrowed<'a, T>> for Owned<T> {
    fn from(t: MaybeBorrowed<'a, T>) -> Self {
        Owned(t.into_or_clone())
    }
}

#[derive(Clone, Copy, Debug, Eq)]
pub enum MaybeBorrowed<'a, B> {
    Borrowed(&'a B),
    Owned(B),
}

impl<'l, 'r, L, R> PartialEq<MaybeBorrowed<'r, R>> for MaybeBorrowed<'l, L>
where
    L: PartialEq<R>,
{
    fn eq(&self, other: &MaybeBorrowed<'r, R>) -> bool {
        **self == **other
    }
}

impl<'a, B> From<B> for MaybeBorrowed<'a, B> {
    fn from(b: B) -> Self {
        Self::Owned(b)
    }
}
impl<'a, B> From<&'a B> for MaybeBorrowed<'a, B> {
    fn from(b: &'a B) -> Self {
        Self::Borrowed(b)
    }
}

impl<'a, B: Clone> MaybeBorrowed<'a, B> {
    pub fn into_or_clone(self) -> B {
        match self {
            Self::Borrowed(b) => b.clone(),
            Self::Owned(b) => b,
        }
    }
}
impl<'a, B> MaybeBorrowed<'a, B> {
    pub fn borrow(&'a self) -> Self {
        Self::Borrowed(&*self)
    }
}

impl<'a, B> Borrow<B> for MaybeBorrowed<'a, B> {
    fn borrow(&self) -> &B {
        &*self
    }
}

impl<'a, B> Deref for MaybeBorrowed<'a, B> {
    type Target = B;
    fn deref(&self) -> &B {
        match self {
            Self::Borrowed(b) => b,
            Self::Owned(ref b) => b,
        }
    }
}

pub trait VebKey: Clone + Ord {
    type High: Clone + Ord;
    type Low: Clone + Ord;

    fn split<'o, F, R>(_v: MaybeBorrowed<'o, Self>, _f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R;
    fn join<'a>(_hi: MaybeBorrowed<'a, Self::High>, _lo: MaybeBorrowed<'a, Self::Low>) -> Self;
}

impl VebKey for () {
    type High = ();
    type Low = ();
    #[inline(always)]
    fn split<'o, F, R>(_v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Owned;
        f(Owned(()), Owned(()))
    }
    #[inline(always)]
    fn join<'a>(_hi: MaybeBorrowed<'a, Self::High>, _lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        ()
    }
}

impl VebKey for u128 {
    type High = [u8; 8];
    type Low = [u8; 8];
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        let [hi@.., _, _, _, _, _, _, _, _] = v.to_ne_bytes();
        let [_, _, _, _, _, _, _, _, lo@..] = v.to_ne_bytes();
        f(MaybeBorrowed::Owned(hi), MaybeBorrowed::Owned(lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let ([hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7], [lo0, lo1, lo2, lo3, lo4, lo5, lo6, lo7]) = (hi.into_or_clone(), lo.into_or_clone());
        u128::from_ne_bytes([hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, lo0, lo1, lo2, lo3, lo4, lo5, lo6, lo7])
    }
}

impl VebKey for i128 {
    type High = [u8; 8];
    type Low = [u8; 8];
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        let [hi@.., _, _, _, _, _, _, _, _] = v.to_ne_bytes();
        let [_, _, _, _, _, _, _, _, lo@..] = v.to_ne_bytes();
        f(MaybeBorrowed::Owned(hi), MaybeBorrowed::Owned(lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let ([hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7], [lo0, lo1, lo2, lo3, lo4, lo5, lo6, lo7]) = (hi.into_or_clone(), lo.into_or_clone());
        i128::from_ne_bytes([hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, lo0, lo1, lo2, lo3, lo4, lo5, lo6, lo7])
    }
}

impl VebKey for u64 {
    type High = u32;
    type Low = u32;
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Owned;
        let v = v.into_or_clone();
        f(Owned((v >> 32) as u32), Owned(v as u32))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let (hi, lo) = (hi.into_or_clone() as u64, lo.into_or_clone() as u64);
        hi << 32 | lo
    }
}

impl VebKey for i64 {
    type High = u32;
    type Low = u32;
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Owned;
        let v = v.into_or_clone() as u64;
        u64::split(Owned(v), f)
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        u64::join(hi, lo) as i64
    }
}

impl VebKey for u32 {
    type High = u16;
    type Low = u16;
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Owned;
        let v = v.into_or_clone();
        f(Owned((v >> 16) as u16), Owned(v as u16))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let (hi, lo) = (hi.into_or_clone() as u32, lo.into_or_clone() as u32);
        hi << 16 | lo
    }
}

impl VebKey for i32 {
    type High = u16;
    type Low = u16;
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Owned;
        let v = v.into_or_clone() as u32;
        u32::split(Owned(v), f)
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        u32::join(hi, lo) as i32
    }
}

impl VebKey for u16 {
    type High = u8;
    type Low = u8;
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Owned;
        let v = v.into_or_clone();
        f(Owned((v >> 8) as u8), Owned(v as u8))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let (hi, lo) = (hi.into_or_clone() as u16, lo.into_or_clone() as u16);
        hi << 8 | lo
    }
}

impl VebKey for i16 {
    type High = u8;
    type Low = u8;
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Owned;
        let v = v.into_or_clone() as u16;
        u16::split(Owned(v), f)
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        u16::join(hi, lo) as i16
    }
}

impl VebKey for u8 {
    type High = U4;
    type Low = U4;
    #[inline(always)]
    fn split<'o, F, R>(_v: MaybeBorrowed<'o, Self>, _f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        todo!()
    }
    #[inline(always)]
    fn join<'a>(_hi: MaybeBorrowed<'a, Self::High>, _lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        todo!()
    }
}

impl VebKey for i8 {
    type High = I4;
    type Low = I4;
    #[inline(always)]
    fn split<'o, F, R>(_v: MaybeBorrowed<'o, Self>, _f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        todo!()
    }
    #[inline(always)]
    fn join<'a>(_hi: MaybeBorrowed<'a, Self::High>, _lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        todo!()
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct U4(pub u8);

impl U4 {
    pub const MAX: u8 = u8::MAX >> 4;
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

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct I4(pub i8);

impl From<U4> for I4 {
    fn from(value: U4) -> Self {
        Self(value.0 as i8)
    }
}
impl From<I4> for U4 {
    fn from(value: I4) -> Self {
        Self(value.0 as u8)
    }
}

impl VebKey for U4 {
    type High = U2;
    type Low = U2;
    #[inline(always)]
    fn split<'o, F, R>(_v: MaybeBorrowed<'o, Self>, _f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        todo!()
    }
    #[inline(always)]
    fn join<'a>(_hi: MaybeBorrowed<'a, Self::High>, _lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        todo!()
    }
}

impl VebKey for I4 {
    type High = I2;
    type Low = I2;
    #[inline(always)]
    fn split<'o, F, R>(_v: MaybeBorrowed<'o, Self>, _f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        todo!()
    }
    #[inline(always)]
    fn join<'a>(_hi: MaybeBorrowed<'a, Self::High>, _lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        todo!()
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct U2(pub u8);

impl U2 {
    pub const MAX: u8 = u8::MAX >> 6;
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

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct I2(pub i8);

impl From<U2> for I2 {
    fn from(value: U2) -> Self {
        Self(value.0 as i8)
    }
}
impl From<I2> for U2 {
    fn from(value: I2) -> Self {
        Self(value.0 as u8)
    }
}

impl VebKey for U2 {
    type High = bool;
    type Low = bool;
    #[inline(always)]
    fn split<'o, F, R>(_v: MaybeBorrowed<'o, Self>, _f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        todo!()
    }
    #[inline(always)]
    fn join<'a>(_hi: MaybeBorrowed<'a, Self::High>, _lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        todo!()
    }
}

impl<T: Clone + Ord> VebKey for [T; 2] {
    type High = T;
    type Low = T;
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Borrowed;
        f(Borrowed(&v[0]), Borrowed(&v[1]))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        [hi.into_or_clone(), lo.into_or_clone()]
    }
}

impl<T: Clone + Ord> VebKey for [T; 3] {
    type High = T;
    type Low = [T; 2];
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Borrowed;
        let [hi, lo@ ..] = &*v;
        f(Borrowed(hi), Borrowed(lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let (hi, [lo0, lo1]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi, lo0, lo1]
    }
}
impl<T: Clone + Ord> VebKey for [T; 4] {
    type High = [T; 2];
    type Low = [T; 2];
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Borrowed;
        let [_, _, lo@ ..] = &*v;
        let [hi@.., _, _] = &*v;
        f(Borrowed(hi), Borrowed(lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let ([hi0, hi1], [lo0, lo1]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi0, hi1, lo0, lo1]
    }
}
impl<T: Clone + Ord> VebKey for [T; 5] {
    type High = [T; 2];
    type Low = [T; 3];
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Borrowed;
        let [_, _, lo@ ..] = &*v;
        let [hi@.., _, _, _] = &*v;
        f(Borrowed(hi), Borrowed(lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let ([hi0, hi1], [lo0, lo1, lo2]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi0, hi1, lo0, lo1, lo2]
    }
}
impl<T: Clone + Ord> VebKey for [T; 6] {
    type High = [T; 3];
    type Low = [T; 3];
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Borrowed;
        let [_, _, _, lo@ ..] = &*v;
        let [hi@.., _, _, _] = &*v;
        f(Borrowed(hi), Borrowed(lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let ([hi0, hi1, hi2], [lo0, lo1, lo2]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi0, hi1, hi2, lo0, lo1, lo2]
    }
}
impl<T: Clone + Ord> VebKey for [T; 7] {
    type High = [T; 3];
    type Low = [T; 4];
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Borrowed;
        let [_, _, _, lo@ ..] = &*v;
        let [hi@.., _, _, _, _] = &*v;
        f(Borrowed(hi), Borrowed(lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let ([hi0, hi1, hi2], [lo0, lo1, lo2, lo3]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi0, hi1, hi2, lo0, lo1, lo2, lo3]
    }
}
impl<T: Clone + Ord> VebKey for [T; 8] {
    type High = [T; 4];
    type Low = [T; 4];
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Borrowed;
        let [_, _, _, _, lo@ ..] = &*v;
        let [hi@.., _, _, _, _] = &*v;
        f(Borrowed(hi), Borrowed(lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let ([hi0, hi1, hi2, hi3], [lo0, lo1, lo2, lo3]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi0, hi1, hi2, hi3, lo0, lo1, lo2, lo3]
    }
}
impl<T: Clone + Ord> VebKey for [T; 16] {
    type High = [T; 8];
    type Low = [T; 8];
    #[inline(always)]
    fn split<'o, F, R>(v: MaybeBorrowed<'o, Self>, f: F) -> R
    where
        F: FnOnce(MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) -> R,
    {
        use MaybeBorrowed::Borrowed;
        let [_, _, _, _,_, _, _, _, lo@ ..] = &*v;
        let [hi@.., _, _, _, _, _, _, _, _,] = &*v;
        f(Borrowed(hi), Borrowed(lo))
    }
    #[inline(always)]
    fn join<'a>(hi: MaybeBorrowed<'a, Self::High>, lo: MaybeBorrowed<'a, Self::Low>) -> Self {
        let ([hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7], [lo0, lo1, lo2, lo3, lo4, lo5, lo6, lo7]) = (hi.into_or_clone(), lo.into_or_clone());
        [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, lo0, lo1, lo2, lo3, lo4, lo5, lo6, lo7]
    }
}

