# Chain of Thought Annotation Guide

The goal of this document is to help annotators provide useful annotated Lean solutions to Olympiad problems for use in Numina’s datasets. The ideal annotation has a clear, coherent flow of reasoning in natural language that solves the problem at hand, followed by a step-by-step translation of that reasoning into Lean that preserves the concepts and structure of the natural language proof, while explaining in detail the choice of tactics and Lean lemmas called and how they impact the formal proof.

## The Structure of an Annotation

The annotations are structured in the style of an LLM engaging in chain-of-thought reasoning. An annotation should generally have three main parts:

* An initial segment of text, entirely in natural language, that reasons through the problem in a logically coherent way, proposing and investigating different ideas or approaches, and eventually explaining a complete solution at hand.  
  * This portion can potentially include explorations of promising lines of reasoning that turn out to be dead ends. But if significant portions turn out to be irrelevant to the eventual proof, then before reference to the formal environment begins, the annotation should reiterate a full explanation of the proof without the extraneous details.  
* A segment of text which plans out the formal proof, referencing the logical steps of the informal proof and explaining what tactics and lemmas will be used to replicate that reasoning in the Lean environment. This section should include, alternately:  
  * Bite-sized chunks of informal reasoning.  
  * Informal explanations of Lean tactics and lemmas that can be used to recreate these steps of reasoning.  
  * Small snippets of code demonstrating intermediate results and the sequences of tactics that can be used to progress through proving these and the main goal.  
* Once the entire Lean proof strategy has been described, a single code block that encompasses the entire Lean proof.

Note that as a matter of process, it **may be easier to start with the Lean proof and then work backwards**, producing a line-by-line explanation of each tactic used to place before the final proof and then writing an explanation of the overall proof strategy to go before that as an introduction.

## Natural Language Proof Overview Guidelines

The initial segment of text takes the form of the kind of chain-of-thought reasoning we want the model to produce when thinking through its proof strategy. As such, it should creatively generate ideas for approaches to the problem. But when it has an idea, it should try to systematically make progress until it either concludes the idea is unworkable, or decides the idea leads to a complete proof. Ideally, before the line of reasoning is executed, the generated text should specify criteria that help it understand if the proof approach seems to be meeting success.

Since it’s not always possible to get the right answer on the first try, we should expect that the model will generate some red herrings. For the purposes of generating annotations/correcting machine-generated annotations:

* If an initial reasoning goes in the wrong direction, it should be clearly marked as an exploratory attempt, and a brief explanation should be given as to why it was abandoned.
  * The failed exploration part can be retained but should be concise and clear.  
  * If a failed exploration seems totally unworkable or short-circuitable, it might be removed entirely, or reduced to a single sentence.  
* If the original reasoning method works logically, but is not conducive to formalization or is not aligned with the code, you can also explain that and add your own solution process.  
* If there are methods of reasoning that seem promising, but you can write them up and include them yourself, again making it clear that the attempt is exploratory and that it ultimately fails.
  * You can use keywords such as "But Wait" to signal the realization of an issue.

## Tactic Planning Text Guidelines

Once a proof overview has been provided, the annotation should move into a tactic planning section. This section of the annotation should consist of a repeating sequence (color-coded here for ease of understanding) of:

1. Explanations for what needs to be done in a particular step of the Lean proof  
2. An explanation of the tactics, hypotheses, and lemmas will be used at this step to accomplish what is needed.  
3. `A lean code block showing how the code for this looks.`

An example of this can be found in [this file](./AnnotationExamples/ChainOfThought/algebra_19511.md).

## Pitfalls to look out for

* **Make sure calculations are correct**. It is common for LLMs to make small arithmetic mistakes with, for example, multiplication or factorization. These can derail the chain of reasoning, leading the model to think that a particular approach is unworkable when it is actually the right way to go, so be sure to look out for these.
* **Make sure reasoning precedes the answer**. The benefit of "chain-of-thought" reasoning is that it allows the model to make logical connections between different parts of the proof *before* arriving at how a segment of the formal proof should look. But when the model is asked to go in the reverse direction and create a natural language explanation of a formal proof, the natural way for it to do this is to state an excerpt of the formal proof *and then* explain it. This is unfortunate, because this explanation is now in the wrong order from what would be beneficial for the model to learn from. So it is sometimes necessary to rearrange explanations so that they are in the most straightforward order for an LLM to generate.
  * On a related note - **Make sure the right parts of the proof correspond to the right explanations**. Sometimes, the model seems to understand the proof, but it will write an overly verbose explanation of a long segment of the proof, so that it's not obvious what steps correspond to what reasoning. In these cases, it's an improvement to break the proof into smaller segments and make the parts of the explanation better correspond to segments.
* **Don't let the model repeat itself too frequently**. Once an LLM gets in the rhythm of writing an explanation it has basically explained before, it can get into a loop of repeating itself. Avoid this by deleting parts of the explanation that are redundant, or by rephrasing them to be more concise.