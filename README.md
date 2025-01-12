# annotation-examples

This repository contains a comprehensive set of guidelines to follow while formalizing problem statements and solutions for Project Numina on our internal platform https://app.projectnumina.ai/. For clarity, we provide a set of examples following the guidelines under the folder `/AnnotationExamples`


1. Using pre-generated auto-formalization output for this solution and paste it into the Lean 4 file after the comments. If incorrect, please correct or fully rewrite the statement in Lean. We will ask you to evaluate its correctness using **TRUE/FALSE** outputs after the annotation is finished.

Examples of autoformalizations (and their corrected versions) are given in the `/AnnotationExamples/Statements` folder
2. If tasked with formalization of the solution, please verify the informal solution in Markdown. If incorrect or imprecise, please add your own edited Markdown solution on the web platform before proceeding to the Lean formalization.
3. If tasked with formalizing the solution, we ask the annotators to generate a **self-contained** solution of the problem using imports from Mathlib. In particular, please do not use auxiliary `def` and `lemma` statements when formalizing the solution.

Additionally, we require the annotators to intersperse steps in the informal solution between Lean 4 code snippets as comments, aligning the informal and the formal solutions. If the formal solution is significantly more detailed, do not hesitate to add extra comments. 

The formal proofs should contain **all key mathematical reasoning steps** from the informal solutions but we are aware that the time-constraint will require some problems to be formalized only *partially*. To provide such *partial* solutions, we expect annotators to use `have` and `suffices` statements. These should be appropriately commented by using an appropriate snippet taken from the informal proof or an annotator description. Naturally, some of proofs of these sub-statements will be completed only partially and contain `sorry` tactics. For this, we provide a quick check-list to follow before using a `sorry` within a proof.

    i. Does there exist a valid Lean proof from the current goal state? If **not** certain, please proceed with the formalization. Else, continue with the check-list.
    ii. Is the proof from the current goal state require mathematically non-trivial reasoning? If **not**, please continue with the formalization. Else, continue with the check-list.
    iii. Is the proof from the current goal require only routine and tedious proof-steps, which cannot be completed within 2-3 lines of Lean code. If **yes**, then `sorry` may be used here to save time. Else, please provide a short-proof from the current goal-state.

A formalization of a solution following these guidelines can be found in the folder `/AnnotationExamples/Solutions`

4. Currently, we are able to compensate for 15 minutes per statement annotation and 1.5 hours per solution annotation. You are encouraged but certainly not expected to keep working on the annotations past these time-frames if that may result in better data quality collected. Please keep these time constraints in mind and budget your time efficiently, while working on the annotations.
