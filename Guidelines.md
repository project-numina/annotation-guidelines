
# Numina Guidelines for formalizing Olympiad-style Problems in Lean

The goal of this document is to help annotators provide useful annotated Lean solutions to Olympiad problems for use in Numina's datasets.
The ideal Lean4 proof is based on a provided human-understandable informal proof, and intersperses the steps of the informal solution within the Lean 4 code as comments, aligning the informal and the formal solutions. If the formal solution is significantly more detailed, do not hesitate to add extra comments.

Currently, we are able to compensate for **15 minutes** per statement annotation and **90 minutes** per solution annotation. You are encouraged but certainly not expected to keep working on the annotations past these time-frames if that may result in better data quality collected. Please keep these time constraints in mind and budget your time efficiently, while working on the annotations.

The formal proofs should contain **all key mathematical reasoning steps** from the informal solutions, but we are aware that the time-constraint will require some problems to be formalized only *partially*. To provide such *partial* solutions, we expect annotators to use `have` and `suffices` statements. These should be appropriately commented by using an appropriate snippet taken from the informal proof or an annotator description. Naturally, some proofs of these sub-statements will be completed only partially and contain `sorry` tactics. For this, we provide a quick check-list to follow before using a `sorry` within a proof.

i. Does there exist a valid Lean proof from the current goal state? If **not** certain, please proceed with the formalization. Else, continue with the check-list.

ii. Is the proof from the current goal state require mathematically non-trivial reasoning? If **not**, please continue with the formalization. Else, continue with the check-list.

iii. Is the proof from the current goal require only routine and tedious proof-steps, which cannot be completed within 2-3 lines of Lean code. If **yes**, then `sorry` may be used here to save time. Else, please provide a short-proof from the current goal-state.

## The Structure of the Lean File

Lean code should import Mathlib via the command `import Mathlib` rather than by importing several specific files.

The natural-language statement of the problem should be placed in a doc-string comment immediately before the statement of the theorem.

It is **strongly discouraged** to use auxiliary definitions and lemmas for the formalization. If **absolutely** needed, you may use them via the **def/lemma** keywords to answer a multiple-choice question, a function/predicate, a common lemma, etc. Such statements should also have a header doc-string in `/-- -/` brackets.

If you do use auxiliary `def` or `lemma` in your formalization, please wrap your submission in a namespace following the convention `(problem_type)_(problem_number)`. An example of this is given in the [`/AnnotationExamples/Statements/namespace_example.lean` file](./AnnotationExamples/Statements/namespace_example.lean), along with an example of how we prefer these auxiliary definitions should be included - as hypotheses to the theorem in question.

## Choice of Numeric Types

There are often a variety of ways to formalize the types of numeric values in Olympiad problems. For example, a problem that references “positive integers” might be formalized using:

* `(n : ℕ+)`  
* `(n : ℕ)` with a hypothesis `(n_pos : 0 < n)`  
* `(n : ℤ)` with a hypothesis `(n_pos : 0 < n)`

We offer the following guidance:

* Attempt to suit the type to the purposes of the problem. For example  
  * If a number is a “positive integer”, but subtractions of or from the value occur in the problem, then it will likely be convenient to formalize this with `ℤ`  
  * On the other hand, if the problem involves exponentiation by this value, it is likely convenient to use `ℕ` so that underlying type will be the same as the type of the base.  
  * If both subtraction and exponentiation occur, then it might be necessary to work with both types. This can be done by using for the base type in the problem statement, and casting to an integer, using `zify` when necessary,
    * e.g. `(n : ℕ) (h : ((n : ℤ) - 1) ^ n)`  
* Avoid using types other than `ℕ`, `ℤ`, `ℚ`, `ℝ`, and `ℂ`  
  * An exception to this might be if the type appears in the domain of a function, in which case, it might be useful to use `ℕ+` to avoid discrepancy about the existence of certain elements of the domain.

## Computation-Heavy Tactics

Lean provides a variety of tactics of varying strength. 
In some cases, it may even be possible to let a tactic such as `interval_cases`, `decide`, or `norm_num` undertake a large case search or numerical computation,
and this can often be the most efficient and concise way to close a goal. 
At the same time, it is important to note that computations in the Lean tactic mode run slower than in most other programming languages, 
and if we allow many computation-heavy proofs in a large dataset, they can easily come to dominate the compile-time of the dataset. 
Additionally, we are interested in approaches that synergize well with natural language, and with the way a human might produce a proof.
A computation-heavy tactic can leave the proof in a state where a human reader is not convinced of the correctness without live access to feedback from Lean. 
But on the other hand, a more verbose explanation of a fact that would otherwise be proved by a single tactic can direct a reader's attention away from the key parts of a proof.

Given these considerations, it can be an important to decide whether a particular goal is best dealt with by a concise computation-heavy tactic or a more verbose proof that avoids computation.
Use the following rules of thumb when choosing whether to use a concise, computation-heavy tactic:

* For computations that require only 10 or fewer cases or arithmetic operations (e.g. to prove the goal `9^9 % 10 = 9`), it is fine to use a single tactic.
* For computations that require ~100 operations, it might be fine to use a computation-heavy tactic, depending on whether or not it significantly increases the total compile time of the proof. 
  * In these cases, the code should be commented with an explanation of the tactic and why we expect that it will finish in a reasonable amount of time.
* Computations that require thousands, miliions or more operations should be avoided.
  * Typically, in the context of an exam problem, there will be some other trick that allows the human solver to draw the conclusion that the computation would provide. Try to formalize the reasoning behind this trick in explicit Lean code.
  * For example, to prove a goal like `9^(9^9) % 10 = 9`, one could perhaps invoke a theorem saying that `9 = (-1 : ZMod 10)` to simplify things.

Some more notes and tips about particular tactics can be found in our [Tactic Cheat Sheet](./FormalizationResources/TacticCheatSheet.md).

## Commonly used `mathlib` definitions to know

* `IsLeast`/`IsGreatest`: These definitions allow you to assert that a particular value is the minimum / maximum of a set. They are often used in problems that involve finding the minimum or maximum value satisfying some property.
* `SimpleGraph`: Some problems involve graphs, or can be stated most naturally in terms of graphs. The `SimpleGraph` definition is a good way to formalize these problems, as it allows you to work with the graph structure directly.
* `EuclideanSpace ℝ (Fin 2)`: Geometric problems are often stated in terms of the Euclidean Plane - this snippet is the conventional way to define this space.

## Other Style References

These guidelines are adapted from, but more specific than, [Joseph Myers’ guidelines for IMO formalization](https://github.com/jsm28/IMOLean). See also [this earlier document](./OldGuidelines.md). In addition to the notes in this document, Lean code appearing in annotations should also adhere to the [mathlib4 style guidelines](https://leanprover-community.github.io/contribute/style.html). Examples can be found in the [Annotation Examples folder](https://github.com/project-numina/annotation-guidelines/tree/master/AnnotationExamples).
