# Tips

## editor config

If you are using an external editor like VS Code for annotation. It suggested that you enable text-wrapping. Since copied Markdown code will appear on a single line in most cases. Adding text wrapping allows you to still be able to read the whole proof without manually putting in newlines at each line.

## `case` bashing

When doing case work on natural numbers or integers, `omega` combined with `rcases` is often useful to get the specific breakdown of cases you want e.g.:

```lean
rcases (by omega : n = 0 ∨ n = 1 ∨ n ≥ 2) with h1 | h2 | h3
. sorry
. sorry
. sorry
```

Additionally, when closing goals related to types with Decidable equality or inequalities (such as `Nat` or `Int`) where there are no free variables or quantified variables, the goal can often be closed using decide.
For example the following result can be proved via decide

```lean
example : (3 = 0 ↔ 2 = 0) ∧ ¬5 = 0 := by decide
```

## `zify`, `qify`, `rify`

Often we have fractional expressions that reduce to integer values. However, it is much easier to prove identities when treating them as fractions rather as integers with floor division.
As such, we can use the `qify` to lift problems from `Int` or `Nat` to `Rat` and use `Nat.cast_div` or `Int.cast_div` as well as `push_cast` and `norm_cast` to simplify expression.

```lean
example (a b c d : Int) : (a / b) / (c / d) = (a * d) / (b * c) := by
  qify
  have h1 : (b * c) ∣ (a * d) := sorry
  have h2 : d ∣ c := sorry
  have h3 : b ∣ a := sorry
  have : (c / d) ∣ a / b := sorry
  push_cast [h1, h2, h3, this]
  field_simp
  ...
```

Similarly, when dealing with subtraction of natural numbers it often easier to first lift into `Int` using `zify` and then use `Nat.cast_sub` and `push_cast`.
Additionally, `rify` can be used to lift problems into `Real`.

## Inspecting tactics

A lot of the time automation tactics like `linarith, omega` will use very helpful lemmas. Putting `show_term` before a tactic can be used to see what a tactic is doing under the hood.
