use alloc::boxed::Box;
use ghost::phantom;

use crate::{
    bitset::{ByteSetMarker, ByteTreeMarker, VecDequeMarker},
    collection::array::ArrayTreeCollectionMarker,
    tree::{TreeMarker, VebTreeMarker},
};

#[phantom]
pub struct BoxMarker<T>;

impl<K, V, T: VebTreeMarker<K, V>> VebTreeMarker<K, V> for BoxMarker<T> {
    type Tree = Box<T::Tree>;
}

pub type VebTreeType<K, V, T> = <T as VebTreeMarker<K, V>>::Tree;

pub type Marker8Empty = ByteSetMarker;
pub type Marker8 = ByteTreeMarker<VecDequeMarker>;

pub type Marker16Empty = TreeMarker<
    Marker8Empty, // Summary
    ArrayTreeCollectionMarker<
        BoxMarker<
            // Children
            Marker8Empty, // Child "tree"
        >,
    >,
>;
pub type Marker16 = TreeMarker<
    Marker8Empty, // Summary
    ArrayTreeCollectionMarker<
        BoxMarker<
            // Children
            Marker8, // Child "tree"
        >,
    >,
>;

pub type Marker32Empty = TreeMarker<
    Marker16Empty, // Summary
    ArrayTreeCollectionMarker<
        BoxMarker<
            // Children
            Marker16Empty, // Child tree
        >,
    >,
>;
pub type Marker32 = TreeMarker<
    Marker16Empty, // Summary
    ArrayTreeCollectionMarker<
        BoxMarker<
            // Children
            Marker16, // Child "tree"
        >,
    >,
>;

pub type Marker64Empty = TreeMarker<
    Marker32Empty, // Summary
    ArrayTreeCollectionMarker<
        BoxMarker<
            // Children
            Marker32Empty, // Child tree
        >,
    >,
>;
pub type Marker64 = TreeMarker<
    Marker32Empty, // Summary
    ArrayTreeCollectionMarker<
        BoxMarker<
            // Children
            Marker32, // Child "tree"
        >,
    >,
>;

// //VebTree
// type U32Marker = TreeMarker<
//     TreeMarker<ByteSetMarker, ByteCollectionMarker<VecDequeMarker, ByteSetMarker>>, // Summary
//     // Children
//     ArrayTreeCollectionMarker<BoxMarker<
//         TreeMarker<ByteSetMarker, ByteCollectionMarker<VecDequeMarker, ByteSetMarker>>, // Child "tree"
//     >>,
// >;
// type U32Marker = TreeMarker<
//     TreeMarker<ByteSetMarker, ArrayTreeCollectionMarker<BoxMarker<ByteSetMarker>>>, // Summary
//     // Children
//     ArrayTreeCollectionMarker<BoxMarker<
//         TreeMarker<ByteSetMarker, ArrayTreeCollectionMarker<BoxMarker<ByteSetMarker>>>, // Child "tree"
//     >>,
