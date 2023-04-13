use core::hash::{BuildHasher, Hash};

use ghost::phantom;
use hashbrown::hash_map::DefaultHashBuilder;
use hashbrown::HashMap;

use crate::{collection::VebTreeCollectionMarker, key::VebKey, tree::VebTreeMarker};

#[phantom]
pub struct HashMapMarker<#[invariant] Tree = (), #[invariant] S = DefaultHashBuilder>;

impl<K, V, Tree, S> VebTreeCollectionMarker<K, V> for HashMapMarker<Tree, S>
where
    K: VebKey,
    K::High: Hash,
    Tree: VebTreeMarker<K::Low, V>,
    S: BuildHasher + Default,
{
    type TreeCollection = HashMap<K::High, Tree::Tree, S>;
}

#[cfg(test)]
mod test {
    // use hashbrown::HashMap;

    // use crate::VebTree;

    // #[test]
    // fn simple() {
    //     type U16Tree = HashMap<u16, ()>;
    //     let mut v = U16Tree::from_monad(10, ());

    //     assert_eq!(v.find(10), Some((&10, &())));
    //     assert_eq!(v.find(11), None);
    //     v.insert(13, ());
    //     assert_eq!(v.find(13), Some((&13, &())));
    //     assert_eq!(v.predecessor(14), Some((&13, &())));
    //     assert_eq!(v.min_val(), (&10, &()));
    //     assert_eq!(v.max_val(), (&13, &()));

    //     v.insert(5, ());
    //     assert_eq!(v.min_val(), (&5, &()));
    // }
}
