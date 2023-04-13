use alloc::boxed::Box;
use ghost::phantom;

use crate::tree::VebTreeMarker;

#[phantom]
pub struct BoxMarker<#[invariant] T>;

impl<K, V, T: VebTreeMarker<K, V>> VebTreeMarker<K, V> for BoxMarker<T> {
    type Tree = Box<T::Tree>;
}

pub type VebTreeType<K, V, T> = <T as VebTreeMarker<K, V>>::Tree;