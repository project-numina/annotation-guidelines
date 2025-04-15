# Tactic Cheat Sheet

A full list of tactics available can be found [in the Mathlib manual here](https://leanprover-community.github.io/mathlib-manual/html-multi/Tactics/All-tactics/#all_tactics). This file provides some notes about the use and description of specific tactics:

## Useful tactics for Olympiad Formalization

* `wlog`: This tactic can be critically helpful in cases where a without loss of generality argument is applied, but take care to think through and describe how the arguments to the hypothesis `wlog` generates are permuted.  
* `hint`: This tactic runs a number of other tactics to attempt to close a goal. It can be useful when you think a goal is likely a one-liner, but you are not immediately sure what approach will work.
* `zify`/`qify`: As mentioned in the main guidelines, these tactics can be useful when it’s necessary to work with the same term cast to different types. We encourage using this tactic (and introducing any lemmas necessary for it to work) earlier in the proof rather than later, so that reasoning step that depend on the enhanced structure it provides are available for more of the proof.

## Notes about specific tactics and how to use/document them

* `native_decide`: try to avoid this tactic, as it relies on [expanding the trusted computing base underlying the theorem](https://leanprover-community.github.io/mathlib-manual/html-multi//Tactics/All-tactics/#native_decide). Use `decide` instead where possible, though even that should be avoided if it is too computationally intensive.  
* `linarith` / `nlinarith`: Is is usually fine to describe these as “linear arithmetic”, but it can improve the efficiency and readability of these tactics to use the `linarith only` version (this requires you to provide the tactic with the hypotheses it should operate on)
* `simp`/`aesop`: These tactics are fine to use, but if a large amount of simplification is being done, describe in a comment the main changes that the tactic is making in its simplifications/resolution of the goal.  
* `constructor` / `by_contra` / `positivity` / `tauto` /`ring`: These tactics are all fairly simple, if you are describing their behavior in natural language, if any comment to elaborate one of these is necessary, 1-3 words should be good enough (i.e. “in the first/second goal”, “by contradiction”, “this expression is structurally positive”, “this is a tautology”, “by normalizing the expression”.)  
* `obtain`/`rcases`/`cases`/`rintro`: As some on the Lean Zulip forum have noted, these tactics largely do similar things, though there are slight differences. Annotators should feel free to use whichever one is best suited to the style of the problem at hand.  
