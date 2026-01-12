## 2024-05-23 - Avoiding `mem::take` on empty collections
**Learning:** In hot loops, unconditionally calling `mem::take` on a `Vec` (or similar collection) to iterate over it involves unnecessary memory writes (replacing with default) and can prevent capacity reuse if the vector is dropped and re-allocated. Checking `is_empty()` first is a cheap read that avoids this overhead.
**Action:** When using the `mem::take` pattern for iteration to satisfy the borrow checker, always check `is_empty()` first if the collection is frequently empty.

## 2024-05-23 - Iterating fixed arrays vs Bitmasks
**Learning:** Iterating over small fixed arrays (like `[VecDeque; 6]`) in hot paths (`pop` operations) can be slower than using a bitmask and CPU instructions (`leading_zeros`) to directly index the relevant element, even if the array is small. Branch prediction and memory access patterns matter.
**Action:** For priority queues with a small, fixed number of levels, use a bitmask to track non-empty levels instead of iterating.

## 2024-05-23 - Unstable sort vs Stable sort
**Learning:** `sort_by_key` in Rust (stable sort) allocates a vector of keys. In hot paths (like propagators), this allocation is costly. `sort_unstable_by` does not allocate and is generally faster if stability is not required.
**Action:** Use `sort_unstable_by` (or `sort_unstable`) when the order of equal elements does not matter, especially in hot loops.
