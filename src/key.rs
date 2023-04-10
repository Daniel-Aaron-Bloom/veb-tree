use core::{ops::Deref, borrow::Borrow, ops::{Shl, Shr, BitOr}};

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

#[derive(Clone, Copy, Debug)]
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

    pub fn clone(&self) -> B {
        (**self).clone()
    }
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
    type High: Clone + Ord + for<'a> Into<Self::HValue<'a>>;
    type Low: Clone + Ord + for<'a> Into<Self::LValue<'a>>;
    type HValue<'a>: Borrow<Self::High> + Into<Owned<Self::High>>
    where
        Self: 'a;
    type LValue<'a>: Borrow<Self::Low> + Into<Owned<Self::Low>>
    where
        Self: 'a;

    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a;
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self;
}

impl VebKey for () {
    type High = ();
    type Low = ();
    type HValue<'a> = ();
    type LValue<'a> = ();
    fn split<'a>(
        _v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        (().into(), ().into())
    }
    fn join(_hi: Self::HValue<'_>, _lo: Self::LValue<'_>) -> Self {
        ()
    }
}

impl VebKey for u128 {
    type High = u64;
    type Low = u64;
    type HValue<'a> = u64;
    type LValue<'a> = u64;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        ((v >> 64) as u64, v as u64)
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        (hi as u128) << 64 | lo as u128
    }
}

impl VebKey for i128 {
    type High = i64;
    type Low = i64;
    type HValue<'a> = i64;
    type LValue<'a> = i64;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        let (lo, hi) = u128::split(v as u128);
        (lo as i64, hi as i64)
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        u128::join(hi as u64, lo as u64) as i128
    }
}

impl VebKey for u64 {
    type High = u32;
    type Low = u32;
    type HValue<'a> = u32;
    type LValue<'a> = u32;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        ((v >> 32) as u32, v as u32)
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        (hi as u64) << 32 | lo as u64
    }
}

impl VebKey for i64 {
    type High = i32;
    type Low = i32;
    type HValue<'a> = i32;
    type LValue<'a> = i32;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        let (lo, hi) = u64::split(v as u64);
        (lo as i32, hi as i32)
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        u64::join(hi as u32, lo as u32) as i64
    }
}

impl VebKey for u32 {
    type High = u16;
    type Low = u16;
    type HValue<'a> = u16;
    type LValue<'a> = u16;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        ((v >> 16) as u16, v as u16)
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        (hi as u32) << 16 | lo as u32
    }
}

impl VebKey for i32 {
    type High = i16;
    type Low = i16;
    type HValue<'a> = i16;
    type LValue<'a> = i16;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        let (lo, hi) = u32::split(v as u32);
        (lo as i16, hi as i16)
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        u32::join(hi as u16, lo as u16) as i32
    }
}

impl VebKey for u16 {
    type High = u8;
    type Low = u8;
    type HValue<'a> = u8;
    type LValue<'a> = u8;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        ((v >> 8) as u8, v as u8)
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        (hi as u16) << 8 | lo as u16
    }
}

impl VebKey for i16 {
    type High = i8;
    type Low = i8;
    type HValue<'a> = i8;
    type LValue<'a> = i8;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        let (lo, hi) = u16::split(v as u16);
        (lo as i8, hi as i8)
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        u16::join(hi as u8, lo as u8) as i16
    }
}

impl VebKey for u8 {
    type High = U4;
    type Low = U4;
    type HValue<'a> = U4;
    type LValue<'a> = U4;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        ((v >> 4).into(), v.into())
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        u8::from(hi) << 4 | u8::from(lo)
    }
}

impl VebKey for i8 {
    type High = I4;
    type Low = I4;
    type HValue<'a> = I4;
    type LValue<'a> = I4;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        let (lo, hi) = u8::split(v as u8);
        (lo.into(), hi.into())
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        u8::join(hi.into(), lo.into()) as i8
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
    type HValue<'a> = U2;
    type LValue<'a> = U2;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        ((v >> 2).into(), v.into())
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        U4::from(hi) << 2 | U4::from(lo)
    }
}

impl VebKey for I4 {
    type High = I2;
    type Low = I2;
    type HValue<'a> = I2;
    type LValue<'a> = I2;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        let (lo, hi) = U4::split(U4::from(v));
        (lo.into(), hi.into())
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        I4::from(U4::join(hi.into(), lo.into()))
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
    type HValue<'a> = bool;
    type LValue<'a> = bool;
    fn split<'a>(
        v: impl 'a + Borrow<Self> + Into<Owned<Self>>,
    ) -> (Self::HValue<'a>, Self::LValue<'a>)
    where
        Self: 'a,
    {
        let Owned(v) = v.into();
        (v >> 1 == U2::from(1), v.into())
    }
    fn join(hi: Self::HValue<'_>, lo: Self::LValue<'_>) -> Self {
        U2::from(hi as u8) << 2 | U2::from(lo as u8)
    }
}
