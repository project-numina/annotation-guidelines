
# Tactic Planning Text Example

Here’s an example of what a tactic planning section could look like, based on [this problem](https://app.projectnumina.ai/problems/38240e48-779f-5d1c-b0d7-b7bee5098700) from the Numina database.

--------

# Solving $\left(\frac{1}{25}\right)^{x + 2} = 125^{-x}$ for $x$

To solve the equation $\left(\frac{1}{25}\right)^{x + 2} = 125^{-x}$, we need to find the value of $x$ that satisfies it. Let's reason through this step by step.

First, I'll express both sides of the equation with the same base. Note that $25 = 5^2$ and $125 = 5^3$. Therefore:

1\. $\left(\frac{1}{25}\right)^{x + 2} = \left(5^{-2}\right)^{x+2} = 5^{-2(x+2)} = 5^{-2x - 4}$  
2\. $125^{-x} = (5^3)^{-x} = 5^{3(-x)} = 5^{-3x}$

Now, we have $5^{-2x - 4} = 5^{-3x}$. Since the bases are the same, we can equate the exponents:

$-2x - 4 = -3x$

Solving for $x$: $-2x - 4 = -3x$ $-2x + 3x - 4 = 0$ $x - 4 = 0$ $x = 4$

So the solution is $x = 4$. Let's verify by substituting back into the original equation:

$\left(\frac{1}{25}\right)^{4 + 2} = \left(\frac{1}{25}\right)^6 = 25^{-6}$ $125^{-4} = (5^3)^{-4} = 5^{-12}$

And $25^{-6} = (5^2)^{-6} = 5^{-12}$, which equals $125^{-4}$.

Therefore, $x = 4$ is indeed the correct solution.

In Lean 4, we would prove this as follows:

````tactics  
import Mathlib  
/-Solve for $x$: $$\left(\frac{1}{25}\right)^{x + 2} = 125^{-x}.$$-/  
theorem algebra_19511 (x : ℤ): (1 / 25 : ℝ) ^ (x + 2) = 125 ^ (-x) ↔ x = 4 := by  
````

We need to prove the equivalence between the equation and x = 4\. Let's start by breaking it into directions using the `constructor` tactic.

````tactics  
  constructor
````

Now we need to manipulate the given equation to find x. As we determined, $\left(\frac{1}{25}\right)^{x + 2} = 5^{-2(x+2)} = 5^{-2x - 4}$ and $125^{-x} = 5^{-3x}$. So we rewrite both sides with base 5\. We can do this by using the \`rw\` tactic, discharging side goals with `norm_num` and using `zpow_mul` to bring all exponents over the same base. We can then put the exponents in normal form with the `ring_nf` tactic.

````tactics

  . intro h
    rw [show (1 / 25 : ℝ) = 5 ^ (-2 : ℤ)  by norm_num, 
          show (125 : ℝ) = 5 ^ (3: ℤ) by norm_num,
          ← zpow_mul,← zpow_mul] at h  
    ring_nf at h`  
````

After substituting, we have $5^{-2(x+2)} = 5^{3(-x)}$ which simplifies to $5^{-2x-4} = 5^{-3x}$.

Then we can equate the exponents, applying the fact that the power function is injective: $-2x-4 = -3x$.

````tactics  
    rw [zpow_right_inj₀] at h
````

Now we need to solve for x in Lean. As we stated before, this is achieved by rearranging the expression $-2x-4 = -3x$, and this can be proved by a simple application of \`linear\_combination\`.

````tactics  
    linear_combination h
````

Now we need to verify conditions for the lemma `zpow_right_inj₀`, namely $0 < 5$ and $5 \neq 1$ which can each be done with `linarith`

````tactics  
    linarith
    linarith
````

Now for the reverse direction:

````tactics  
  . intro h
````

Substituting x = 4 into the left side: $\left(\frac{1}{25}\right)^{4+2} = \left(\frac{1}{25}\right)^6 = 25^{-6}$ Substituting x = 4 into the right side: $125^{-4} = (5^3)^{-4} = 5^{-12}$ And $25^{-6} = (5^2)^{-6} = 5^{-12}$,

````tactics  
    rw [h]
````

so both sides equal. In Lean, the `norm_num` tactic can compute both sides explicitly and verify they are equal when x = 4.

````tactics  
    norm_num
````

Therefore, the solution to the equation is indeed x = 4.
