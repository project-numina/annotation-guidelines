# Common Pitfalls

## Avoiding Junk Values

A common formalization error among beginners (and even experts!) involves "junk values". Functions in Lean return values even on inputs that would normally be considered undefined or outside the domain. Two examples of this are truncated subtraction (i.e. `2 - 5 = 0`) and floor division (i.e. `5 / 2 = 2`) of naturals. This can lead to formalizations that do not match the intended meaning of the underlying problem. We recommend double-checking the types in the editor to ensure they are what is expected.

The best way to deal with this problem when unwanted is to cast values to the desired type before the operation, (i.e. `(2 : ℤ) - 5 = -3` or `(5 : ℚ) / 2 = ...`). It is not strictly necessary to do this in all cases: For example `n * (n + 1) / 2` is a case where the division will never need to round, so it is acceptable as-is.

## 0-indexing vs 1-indexing

Olympiad problems typically use 1-indexing for finite and infinite sequences. This can cause problems with Lean, which includes `0` in its type of Natural numbers and in the type `Fin n` of naturals below `n`. There are a few potential ways to solve this, depending on the context of the problem:

* Switch to use of 0 indexing: This works best when the indices themselves are not referenced in the problem outside of being used as indices. If the problem does use them (e.g. via a construction like $a_i + i$), this will likely not work well.
* Use `ℕ`, but ignore the 0 element. This often works well, but it can lead to problems if a problem asks you to characterize a set of functions on the positive integers.
* Use `ℕ+`. This makes indexing consistent with the problem, but there is less API around this type.

Choose the option that best fits the problem at hand.