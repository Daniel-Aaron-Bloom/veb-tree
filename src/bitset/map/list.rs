use alloc::collections::VecDeque;

use crate::{MaybeRemoveResult, RemoveResult, TreeKV, VebTree};

pub struct VecDequeMarker;

pub trait TreeListMarker<Tree: VebTree> {
    type List: TreeList<Tree = Tree>;
}

pub type TreeListRemoveResult<TL> = (Option<(TL, bool)>, TreeKV<<TL as TreeList>::Tree>);
pub type TreeListMaybeRemoveResult<TL> = Result<TreeListRemoveResult<TL>, TL>;

pub trait TreeList: Sized {
    type Tree: VebTree;
    fn from_monad(v: Self::Tree) -> Self;

    fn len(&self) -> usize;
    fn get(&self, i: usize) -> &Self::Tree;
    fn get_mut(&mut self, i: usize) -> &mut Self::Tree;
    fn insert_tree(&mut self, i: usize, v: Self::Tree);
    fn remove_key<F>(self, i: usize, f: F) -> TreeListRemoveResult<Self>
    where
        F: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>;
    fn maybe_remove_key<F>(self, i: usize, f: F) -> TreeListMaybeRemoveResult<Self>
    where
        F: FnOnce(Self::Tree) -> MaybeRemoveResult<Self::Tree>;
}

impl<Tree: VebTree> TreeListMarker<Tree> for VecDequeMarker {
    type List = VecDeque<Tree>;
}

impl<V: VebTree> TreeList for VecDeque<V> {
    type Tree = V;

    fn from_monad(v: Self::Tree) -> Self {
        VecDeque::from_iter([v])
    }

    fn len(&self) -> usize {
        self.len()
    }
    fn get(&self, i: usize) -> &Self::Tree {
        &self[i]
    }
    fn get_mut(&mut self, i: usize) -> &mut Self::Tree {
        &mut self[i]
    }
    fn insert_tree(&mut self, i: usize, v: Self::Tree) {
        self.insert(i, v);
    }
    fn remove_key<F>(mut self, i: usize, f: F) -> TreeListRemoveResult<Self>
    where
        F: FnOnce(Self::Tree) -> RemoveResult<Self::Tree>,
    {
        use vec_entry::{Entry, EntryExt};

        let entry = match self.entry(i) {
            Entry::Occupied(o) => o,
            Entry::Vacant(_) => unreachable!(),
        };

        let (_, (val, removed)) = entry.replace_entry_with(|_, tree| {
            let (tree, val) = f(tree);
            let removed = tree.is_none();
            (tree, (val, removed))
        });

        if self.is_empty() {
            debug_assert!(removed);
            (None, val)
        } else {
            (Some((self, removed)), val)
        }
    }
    fn maybe_remove_key<F>(mut self, i: usize, f: F) -> TreeListMaybeRemoveResult<Self>
    where
        F: FnOnce(Self::Tree) -> MaybeRemoveResult<Self::Tree>,
    {
        use vec_entry::{Entry, EntryExt};

        let entry = match self.entry(i) {
            Entry::Occupied(o) => o,
            Entry::Vacant(_) => unreachable!(),
        };

        let (_, removed) = entry.replace_entry_with(|_, tree| match f(tree) {
            Err(tree) => (Some(tree), None),
            Ok((tree, val)) => {
                let removed = tree.is_none();
                (tree, Some((val, removed)))
            }
        });

        match removed {
            Some((val, removed)) if self.is_empty() => {
                debug_assert!(removed);
                Ok((None, val))
            }
            Some((val, removed)) => Ok((Some((self, removed)), val)),
            None => Err(self),
        }
    }
}

pub trait ListMarker<V> {
    type List: List<Value = V>;
}

pub trait List: Sized {
    type Value;
    fn create() -> Self;
    fn len(&self) -> usize;
    fn get(&self, i: usize) -> &Self::Value;
    fn get_mut(&mut self, i: usize) -> &mut Self::Value;
    fn insert_value(&mut self, i: usize, v: Self::Value);
    fn remove_value(self, i: usize) -> (Option<Self>, Self::Value);
}

impl<V> ListMarker<V> for VecDequeMarker {
    type List = VecDeque<V>;
}

impl<V> List for VecDeque<V> {
    type Value = V;
    fn create() -> Self {
        VecDeque::new()
    }
    fn len(&self) -> usize {
        self.len()
    }
    fn get(&self, i: usize) -> &Self::Value {
        &self[i]
    }
    fn get_mut(&mut self, i: usize) -> &mut Self::Value {
        &mut self[i]
    }
    fn insert_value(&mut self, i: usize, v: Self::Value) {
        self.insert(i, v)
    }
    fn remove_value(mut self, i: usize) -> (Option<Self>, Self::Value) {
        let v = self.remove(i).unwrap();
        (if self.is_empty() { None } else { Some(self) }, v)
    }
}
