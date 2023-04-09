use core::ops::Deref;
use std::borrow::Borrow;

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
        (
            ((v >> 64) as u64).into(),
            ((v & u64::MAX as u128) as u64).into(),
        )
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
        (
            ((v >> 32) as u32).into(),
            ((v & u32::MAX as u64) as u32).into(),
        )
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
        (
            ((v >> 16) as u16).into(),
            ((v & u16::MAX as u32) as u16).into(),
        )
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
        (((v >> 8) as u8).into(), ((v & u8::MAX as u16) as u8).into())
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

/*
impl VebKey for i128 {
    type High = i64;
    type Low = i64;
    fn split<'a>(v: impl Into<MaybeBorrowed<'a, Self>>) -> (MaybeBorrowed<'a, Self::High>, MaybeBorrowed<'a, Self::Low>)
    where Self: 'a {
        let v = v.into();
        let (a, b) = u128::split(v as u128);

        a.into_or_clone()

    }
    fn join(hi: MaybeBorrowed<Self::High>, lo: MaybeBorrowed<Self::Low>) -> Self {
        (*hi as i128) << 64 | *lo as i128
    }
}

impl VebKey for u64 {
    type High = u32;
    type Low = u32;
    fn split(v: MaybeBorrowed<Self>) -> (MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) {
        (((&*v >> 32) as u32).into(), ((&*v & u32::MAX as u64) as u32).into())
    }
    fn join(hi: MaybeBorrowed<Self::High>, lo: MaybeBorrowed<Self::Low>) -> Self {
        (*hi as u64) << 32 | *lo as u64
    }
}

impl VebKey for i64 {
    type High = i32;
    type Low = i32;
    fn split(v: MaybeBorrowed<Self>) -> (MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) {
        (((&*v >> 32) as i32).into(), ((&*v & i32::MAX as i64) as i32).into())
    }
    fn join(hi: MaybeBorrowed<Self::High>, lo: MaybeBorrowed<Self::Low>) -> Self {
        (*hi as i64) << 32 | *lo as i64
    }
}

impl VebKey for u32 {
    type High = u16;
    type Low = u16;
    fn split(v: MaybeBorrowed<Self>) -> (MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) {
        (((&*v >> 16) as u16).into(), ((&*v & u16::MAX as u32) as u16).into())
    }
    fn join(hi: MaybeBorrowed<Self::High>, lo: MaybeBorrowed<Self::Low>) -> Self {
        (*hi as u32) << 16 | *lo as u32
    }
}

impl VebKey for i32 {
    type High = i16;
    type Low = i16;
    fn split(v: MaybeBorrowed<Self>) -> (MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) {
        (((&*v >> 16) as i16).into(), ((&*v & i16::MAX as i32) as i16).into())
    }
    fn join(hi: MaybeBorrowed<Self::High>, lo: MaybeBorrowed<Self::Low>) -> Self {
        (*hi as i32) << 16 | *lo as i32
    }
}

impl VebKey for u16 {
    type High = u8;
    type Low = u8;
    fn split(v: MaybeBorrowed<Self>) -> (MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) {
        (((&*v >> 8) as u8).into(), ((&*v & u8::MAX as u16) as u8).into())
    }
    fn join(hi: MaybeBorrowed<Self::High>, lo: MaybeBorrowed<Self::Low>) -> Self {
        (*hi as u16) << 8 | *lo as u16
    }
}

impl VebKey for i16 {
    type High = i8;
    type Low = i8;
    fn split(v: MaybeBorrowed<Self>) -> (MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) {
        (((&*v >> 8) as i8).into(), ((&*v & i8::MAX as i16) as i8).into())
    }
    fn join(hi: MaybeBorrowed<Self::High>, lo: MaybeBorrowed<Self::Low>) -> Self {
        (*hi as i16) << 8 | *lo as i16
    }
}

impl VebKey for u8 {
    type High = U4;
    type Low = U4;
    fn split(v: MaybeBorrowed<Self>) -> (MaybeBorrowed<Self::High>, MaybeBorrowed<Self::Low>) {
        (U4(&*v >> 4).into(), U4(&*v & U4::MAX).into())
    }
    fn join(hi: MaybeBorrowed<Self::High>, lo: MaybeBorrowed<Self::Low>) -> Self {
        (hi.0 << 4 | lo.0)
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct U4(pub u8);

impl U4 {
    pub const MAX: u8 = u8::MAX >> 4;
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct U2(pub u8);


*/
