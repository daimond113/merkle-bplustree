//! Tree shape descriptions and appropriate collection types.

use std::{num::NonZero, ops::RangeInclusive};

use thiserror::Error;

use crate::{HasherOutput, TreeConfig};

/// An array-based growable collection of items.
pub trait OrderedCollection<T>: AsRef<[T]> + AsMut<[T]> + Default {
    /// Inserts an element at an arbitrary index within the collection.
    /// `index` will always be less than or equal to the length of the slice.
    fn insert_at(&mut self, index: usize, element: T);

    /// Appends an element to the end.
    /// By default, this calls [Self::insert_at] with the slice length as the index.
    fn push(&mut self, element: T) {
        self.insert_at(self.as_ref().len(), element);
    }

    /// Appends all elements from `other` to the end of Self, preserving order.
    fn append(&mut self, other: Self);

    /// Removes and returns the element at an arbitrary index within the collection,
    /// shifting all following elements to the left.
    fn remove_at(&mut self, index: usize) -> T;

    /// Mutates self to contain [0, at) elements and returns a new collection with the elements from [at, ..)
    fn split_off(&mut self, at: usize) -> Self;
}

const fn half_ceil(a: NonZero<usize>) -> NonZero<usize> {
    match NonZero::new(a.get().div_ceil(2)) {
        Some(h) => h,
        None => const { NonZero::new(1).unwrap() },
    }
}

const fn max(a: NonZero<usize>, b: NonZero<usize>) -> NonZero<usize> {
    if a.get() > b.get() { a } else { b }
}

/// A description of a B+Tree's shape. The methods of this trait should be cheap to call repeatedly.
pub trait Shaper<C: TreeConfig>: Send + Sync {
    /// The collection for [TreeInternalNode::keys](crate::node::TreeInternalNode::keys).
    /// The maximum amount of these is the maximum amount of internal children - 1.
    type InternalKeys: OrderedCollection<C::Key> + Send + Sync + Clone;
    /// The collection for [TreeInternalNode::children](crate::node::TreeInternalNode::children).
    type InternalChildren: OrderedCollection<HasherOutput<C>> + Send + Sync + Clone;
    /// The collection for [TreeLeafNode::keys](crate::node::TreeLeafNode::keys).
    type LeafKeys: OrderedCollection<C::Key> + Send + Sync + Clone;
    /// The collection for [TreeLeafNode::values](crate::node::TreeLeafNode::values).
    type LeafValues: OrderedCollection<C::Value> + Send + Sync + Clone;

    /// The maximum amount of internal children. Must be at least 3.
    fn max_internal_children(&self) -> NonZero<usize>;
    /// The minimum amount of internal children a non-root node may contain. Must be within [2, half_ceil(max)].
    fn min_internal_children(&self) -> NonZero<usize> {
        half_ceil(self.max_internal_children())
    }

    /// The maximum amount of leaf entries.
    fn max_leaf_entries(&self) -> NonZero<usize>;
    /// The minimum amount of leaf entries a non-root node may contain. Must be within [1, half_ceil(max)].
    fn min_leaf_entries(&self) -> NonZero<usize> {
        half_ceil(self.max_leaf_entries())
    }
}

/// An error in the shaper's configuration.
#[derive(Debug, Error)]
pub enum ShaperValidationError {
    /// The minimum amount of internal children was outside the possible range.
    #[error("minimum amount of internal children must be within {}..={}, but it is {actual}", .range.start(), .range.end())]
    MinimumInternalChildrenOutOfRange {
        /// The range that is supported.
        range: RangeInclusive<NonZero<usize>>,
        /// The value that was described.
        actual: NonZero<usize>,
    },

    /// The minimum amount of leaf entries was larger than the possible amount.
    #[error("minimum amount of leaf entries is {0}, but it must be <= {1}")]
    MinimumLeafEntriesTooLarge(NonZero<usize>, NonZero<usize>),
}

pub(crate) const MIN_INTERNAL_CHILDREN: NonZero<usize> = NonZero::new(2).unwrap();

pub(crate) const fn validate_shaper(
    min_internal_children: NonZero<usize>,
    max_internal_children: NonZero<usize>,
    min_leaf_entries: NonZero<usize>,
    max_leaf_entries: NonZero<usize>,
) -> Result<(), ShaperValidationError> {
    let range = MIN_INTERNAL_CHILDREN..=half_ceil(max_internal_children);
    if min_internal_children.get() < range.start().get()
        || min_internal_children.get() > range.end().get()
    {
        return Err(ShaperValidationError::MinimumInternalChildrenOutOfRange {
            range,
            actual: min_internal_children,
        });
    }

    let min = half_ceil(max_leaf_entries);
    if min_leaf_entries.get() > min.get() {
        return Err(ShaperValidationError::MinimumLeafEntriesTooLarge(
            min_leaf_entries,
            min,
        ));
    }

    Ok(())
}

/// A [Shaper] implementation based on runtime values.
#[derive(Debug, Clone, Copy)]
pub struct RuntimeShaper {
    min_internal_children: NonZero<usize>,
    max_internal_children: NonZero<usize>,
    min_leaf_entries: NonZero<usize>,
    max_leaf_entries: NonZero<usize>,
}

impl RuntimeShaper {
    /// Creates [Self] with the max amounts and defaults minimal amounts to their maximum possible values.
    pub fn with_max(
        max_internal_children: NonZero<usize>,
        max_leaf_entries: NonZero<usize>,
    ) -> Result<Self, ShaperValidationError> {
        let shaper = Self {
            min_internal_children: max(half_ceil(max_internal_children), MIN_INTERNAL_CHILDREN),
            max_internal_children,
            min_leaf_entries: half_ceil(max_leaf_entries),
            max_leaf_entries,
        };
        validate_shaper(
            shaper.min_internal_children,
            shaper.max_internal_children,
            shaper.min_leaf_entries,
            shaper.max_leaf_entries,
        )?;
        Ok(shaper)
    }

    /// Creates [Self] with the min and max amounts.
    pub fn with_min_max(
        min_internal_children: NonZero<usize>,
        max_internal_children: NonZero<usize>,
        min_leaf_entries: NonZero<usize>,
        max_leaf_entries: NonZero<usize>,
    ) -> Result<Self, ShaperValidationError> {
        let shaper = Self {
            min_internal_children,
            max_internal_children,
            min_leaf_entries,
            max_leaf_entries,
        };
        validate_shaper(
            shaper.min_internal_children,
            shaper.max_internal_children,
            shaper.min_leaf_entries,
            shaper.max_leaf_entries,
        )?;
        Ok(shaper)
    }
}

impl<C: TreeConfig> Shaper<C> for RuntimeShaper {
    type InternalKeys = Vec<C::Key>;
    type InternalChildren = Vec<HasherOutput<C>>;
    type LeafKeys = Vec<C::Key>;
    type LeafValues = Vec<C::Value>;

    fn max_internal_children(&self) -> NonZero<usize> {
        self.max_internal_children
    }

    fn min_internal_children(&self) -> NonZero<usize> {
        self.min_internal_children
    }

    fn max_leaf_entries(&self) -> NonZero<usize> {
        self.max_leaf_entries
    }

    fn min_leaf_entries(&self) -> NonZero<usize> {
        self.min_leaf_entries
    }
}

impl<T> OrderedCollection<T> for Vec<T> {
    fn insert_at(&mut self, index: usize, element: T) {
        self.insert(index, element);
    }

    fn push(&mut self, element: T) {
        self.push(element);
    }

    fn append(&mut self, mut other: Self) {
        self.append(&mut other);
    }

    fn remove_at(&mut self, index: usize) -> T {
        self.remove(index)
    }

    fn split_off(&mut self, at: usize) -> Self {
        self.split_off(at)
    }
}

#[cfg(feature = "const")]
impl<T, const CAP: usize> OrderedCollection<T> for arrayvec::ArrayVec<T, CAP> {
    fn insert_at(&mut self, index: usize, element: T) {
        self.insert(index, element);
    }

    fn push(&mut self, element: T) {
        self.push(element);
    }

    fn append(&mut self, other: Self) {
        self.extend(other);
    }

    fn remove_at(&mut self, index: usize) -> T {
        self.remove(index)
    }

    fn split_off(&mut self, at: usize) -> Self {
        self.drain(at..).collect()
    }
}

macro_rules! const_struct {
    (
		$(#[$meta:meta])*
        $shaper:ident,
        $min_internal_children:block,
        $min_leaf_entries:block,
        $($const:ident),+
    ) => {
        #[cfg(feature = "const")]
        $(#[$meta])*
        pub struct $shaper<
            $(const $const: usize),+
        >(());

        #[cfg(feature = "const")]
        impl<$(const $const: usize),+> Default for $shaper<$($const),+> {
            fn default() -> Self {
                const { Self::new() }
            }
        }

        #[cfg(feature = "const")]
        impl<$(const $const: usize),+> $shaper<$($const),+> {
            const fn new() -> Self {
                let shaper = Self(());

                let validation = validate_shaper(
                    $min_internal_children,
                    NonZero::new(MAX_INTERNAL_CHILDREN).unwrap(),
                    $min_leaf_entries,
                    NonZero::new(MAX_LEAF_ENTRIES).unwrap(),
                );
                match validation {
                    Ok(_) => {},
                    Err(ShaperValidationError::MinimumInternalChildrenOutOfRange {..}) => {
                        panic!("minimum amount of internal children is illegal")
                    },
                    Err(ShaperValidationError::MinimumLeafEntriesTooLarge(..)) => {
                        panic!("minimum amount of leaf entries is illegal")
                    }
                }

                if MAX_INTERNAL_KEYS != MAX_INTERNAL_CHILDREN - 1 {
                    panic!("MAX_INTERNAL_KEYS must be equal to MAX_INTERNAL_CHILDREN - 1");
                }

                shaper
            }
        }

        #[cfg(feature = "const")]
        impl<C: TreeConfig, $(const $const: usize),+> Shaper<C> for $shaper<$($const),+> {
            type InternalKeys = arrayvec::ArrayVec<C::Key, MAX_INTERNAL_KEYS>;
            type InternalChildren = arrayvec::ArrayVec<HasherOutput<C>, MAX_INTERNAL_CHILDREN>;
            type LeafKeys = arrayvec::ArrayVec<C::Key, MAX_LEAF_ENTRIES>;
            type LeafValues = arrayvec::ArrayVec<C::Value, MAX_LEAF_ENTRIES>;

            fn max_internal_children(&self) -> NonZero<usize> {
                const { NonZero::new(MAX_INTERNAL_CHILDREN).unwrap() }
            }

            fn min_internal_children(&self) -> NonZero<usize> {
                const $min_internal_children
            }

            fn max_leaf_entries(&self) -> NonZero<usize> {
                const { NonZero::new(MAX_LEAF_ENTRIES).unwrap() }
            }

            fn min_leaf_entries(&self) -> NonZero<usize> {
                const $min_leaf_entries
            }
        }
    };
}

const_struct!(
    /// A const-based [Shaper] configured with maximum values and maximum allowed minimal values.
    MaxConstShaper,
    { half_ceil(NonZero::new(MAX_INTERNAL_CHILDREN).unwrap()) },
    { half_ceil(NonZero::new(MAX_LEAF_ENTRIES).unwrap()) },
    MAX_LEAF_ENTRIES,
    MAX_INTERNAL_CHILDREN,
    MAX_INTERNAL_KEYS
);

const_struct!(
    /// A const-based [Shaper] configured with minimum and maximum values.
    MinMaxConstShaper,
    { NonZero::new(MIN_INTERNAL_CHILDREN).unwrap() },
    { NonZero::new(MIN_LEAF_ENTRIES).unwrap() },
    MIN_LEAF_ENTRIES,
    MAX_LEAF_ENTRIES,
    MIN_INTERNAL_CHILDREN,
    MAX_INTERNAL_CHILDREN,
    MAX_INTERNAL_KEYS
);
