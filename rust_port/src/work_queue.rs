//! Phase 1 — a single-pass FIFO work queue.
//!
//! [`WorkQueue`] is a first-in/first-out worklist for traversals (BFS and the
//! like) that *discover work as they go*: push some seed items, pop them in
//! FIFO order, and push more while draining. It is built once, drained exactly
//! once, and then dropped.
//!
//! # Why not `VecDeque`?
//!
//! Internally it is a flat `Vec` walked with a head index, not a ring buffer.
//! `pop` is an index bump and `push` is an append — neither performs the
//! wraparound arithmetic a `VecDeque` does on every operation. In the hot
//! `PseudoConfiguration::homomorphism` BFS (called millions of times per run)
//! that bookkeeping is measurable: on `enum_wheels d7` the flat worklist ran
//! ~1.16x faster than a pre-sized `VecDeque`, and ~1.5x faster than a
//! `VecDeque::new()` that regrows on each call. Disassembly traced the gap to
//! exactly the per-operation wraparound `csel` sequences a ring buffer emits
//! and this type does not.
//!
//! # The tradeoff: memory is not reclaimed until drop
//!
//! Popped slots are **not** freed or reused — `head` only moves forward, so the
//! `Vec` retains every item ever pushed. Peak memory is the *total* number of
//! pushes over the whole drain, not the number of items live at once. That is
//! what buys the simple, branch-free `pop`, and it is fine for the intended
//! short-lived, bounded traversals. It makes this type a poor fit for:
//!
//! - long-lived or unbounded queues (memory would grow without bound) — use
//!   [`std::collections::VecDeque`];
//! - queues reused across iterations (there is deliberately no `clear`/reset;
//!   allocate a fresh `WorkQueue` per traversal);
//! - anything needing `push_front` / `pop_back` — this is FIFO only.
//!
//! Items are `Copy`: the work items are meant to be small (e.g. index pairs),
//! which also keeps the retain-until-drop cost negligible.

/// A single-pass FIFO worklist. See the [module documentation](self) for the
/// intended use and its tradeoffs.
#[derive(Clone, Debug)]
pub struct WorkQueue<T> {
    items: Vec<T>,
    head: usize,
}

impl<T: Copy> WorkQueue<T> {
    /// A new queue pre-sized for about `cap` total pushes over the whole drain
    /// (since slots are never reclaimed, size for the total, not the peak live
    /// count).
    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        WorkQueue {
            items: Vec::with_capacity(cap),
            head: 0,
        }
    }

    /// Append an item to the back.
    #[inline]
    pub fn push(&mut self, item: T) {
        self.items.push(item);
    }

    /// Remove and return the front item, or `None` once the queue is drained.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let item = self.items.get(self.head).copied()?;
        self.head += 1;
        Some(item)
    }

    /// Whether every pushed item has been popped.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head >= self.items.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fifo_order() {
        let mut q = WorkQueue::with_capacity(4);
        q.push(1);
        q.push(2);
        q.push(3);
        assert_eq!(q.pop(), Some(1));
        assert_eq!(q.pop(), Some(2));
        assert_eq!(q.pop(), Some(3));
        assert_eq!(q.pop(), None);
    }

    #[test]
    fn push_while_draining() {
        // BFS-style: items pushed mid-drain are still processed in FIFO order.
        let mut q = WorkQueue::with_capacity(2);
        q.push(0);
        let mut seen = Vec::new();
        while let Some(x) = q.pop() {
            seen.push(x);
            if x < 3 {
                q.push(x + 1);
            }
        }
        assert_eq!(seen, vec![0, 1, 2, 3]);
    }

    #[test]
    fn is_empty_tracks_drain() {
        let mut q = WorkQueue::with_capacity(1);
        assert!(q.is_empty());
        q.push(7);
        assert!(!q.is_empty());
        q.pop();
        assert!(q.is_empty());
    }
}
