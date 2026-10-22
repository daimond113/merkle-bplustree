use std::borrow::Cow;

use crate::{HasherOutput, TreeConfig, hasher::Hasher as _, proof::InvalidProofError};

pub(crate) fn merkle_root<C: TreeConfig>(
    hashes: impl ExactSizeIterator<Item = HasherOutput<C>>,
) -> HasherOutput<C> {
    let count = hashes.len();
    if count == 0 {
        return C::Hasher::empty_hash();
    }

    let mut buf = Vec::new();
    buf.reserve_exact(count.next_power_of_two());
    buf.extend(hashes);

    merkle_root_in_place::<C>(&mut buf, 0)
}

pub(crate) fn merkle_root_in_place<C: TreeConfig>(
    buf: &mut Vec<HasherOutput<C>>,
    start: usize,
) -> HasherOutput<C> {
    let count = buf.len() - start;
    if count == 0 {
        return C::Hasher::empty_hash();
    }

    let padded = count.next_power_of_two();
    if padded != count {
        buf.resize(start + padded, C::Hasher::empty_hash());
    }

    let mut width = padded;
    while width > 1 {
        width /= 2;
        for i in 0..width {
            buf[start + i] = C::Hasher::merge_hashes(&buf[start + i * 2], &buf[start + i * 2 + 1]);
        }
    }

    let root = buf.swap_remove(start);
    buf.truncate(start);
    root
}

pub(crate) fn merkle_prove<const SKIP: usize, C: TreeConfig>(
    hashes: impl ExactSizeIterator<Item = HasherOutput<C>>,
    mut index: usize,
) -> Box<[HasherOutput<C>]> {
    let count = hashes.len();
    if count == 0 {
        return [].into();
    }

    let padded = count.next_power_of_two();
    let mut buf = Vec::new();
    buf.reserve_exact(padded);
    buf.extend(hashes);
    if padded != count {
        buf.resize(padded, C::Hasher::empty_hash());
    }

    let mut siblings = Vec::new();
    siblings.reserve_exact(padded.trailing_zeros() as usize - SKIP);

    let mut to_skip = SKIP;

    let mut width = padded;
    while width > 1 {
        if to_skip == 0 {
            siblings.push(buf[index ^ 1].clone());
        } else {
            to_skip -= 1;
        }

        width /= 2;
        for i in 0..width {
            buf[i] = C::Hasher::merge_hashes(&buf[i * 2], &buf[i * 2 + 1]);
        }
        index /= 2;
    }

    siblings.into_boxed_slice()
}

pub(crate) fn merkle_root_from<'a, 'b, C: TreeConfig>(
    leaf: Cow<'a, HasherOutput<C>>,
    mut index: usize,
    siblings: impl Iterator<Item = &'b HasherOutput<C>>,
) -> Result<Cow<'a, HasherOutput<C>>, InvalidProofError> {
    let mut current = leaf;

    for sibling in siblings {
        let merged = if index.is_multiple_of(2) {
            C::Hasher::merge_hashes(&current, sibling)
        } else {
            C::Hasher::merge_hashes(sibling, &current)
        };
        current = Cow::Owned(merged);
        index /= 2;
    }

    if index != 0 {
        return Err(InvalidProofError);
    }

    Ok(current)
}
