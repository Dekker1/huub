## 2024-05-23 - Avoiding `mem::take` on empty collections
**Learning:** In hot loops, unconditionally calling `mem::take` on a `Vec` (or similar collection) to iterate over it involves unnecessary memory writes (replacing with default) and can prevent capacity reuse if the vector is dropped and re-allocated. Checking `is_empty()` first is a cheap read that avoids this overhead.
**Action:** When using the `mem::take` pattern for iteration to satisfy the borrow checker, always check `is_empty()` first if the collection is frequently empty.
