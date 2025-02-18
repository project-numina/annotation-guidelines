import Mathlib

open Polynomial
/- Let $P$ and $Q$ be polynomials with integer coefficients. Suppose that the integers $a$ and $a+1997$ are roots of $P$, and that $Q(1998)=2000$. Prove that the equation $Q(P(x))=1$ has no integer solutions. -/
theorem number_theory_64261 {P Q : Polynomial ℤ} (ha : P.eval a = 0) (ha' : P.eval (a + 1997) = 0)
    (hQ : Q.eval 1998 = 2000) :
    ¬∃ x : ℤ, Q.eval (P.eval x) = 1 := by
    -- Let $c$ denote the constant term in $Q(x)$.
    let c := Q.coeff 0
    -- Suppose on the contrary that there exists $n$ such that $Q(P(n))=1$.
    by_contra! h
    obtain ⟨n, hn⟩ := h
    -- Clearly we have $P(x)=(x-a)(x-a-1997)R(x)$ for some polynomial $R(x)$.
    have h1 : ∃ R : Polynomial ℤ, P = (X - C a) * (X - C (a + 1997)) * R := by
      rw [← Polynomial.IsRoot.def, ← Polynomial.dvd_iff_isRoot] at ha
      obtain ⟨R1, hR1⟩ := ha
      have : eval (a + 1997) R1 = 0 := by
        simp [hR1] at ha'
        exact ha'
      rw [← Polynomial.IsRoot.def, ← Polynomial.dvd_iff_isRoot] at this
      obtain ⟨R2, hR2⟩ := this
      use R2
      rw [hR1, hR2]
      ring
    -- Regardless of the parity of $a$ exactly one of $x-a$ and $x-a-1997$ is even, so that  $2|P(x)$ .
    have h2 : ∀ x : ℤ, 2 ∣ P.eval x := by
      intro x
      obtain ⟨R, hR⟩ := h1
      simp [hR]
      apply dvd_mul_of_dvd_left
      -- one of $x-a$ and $x-a-1997$ is even
      have h2' : 2 ∣ (x - a) * (x - a - 1997) := by
        by_cases h : Even (x - a)
        · apply dvd_mul_of_dvd_left 
          rwa [even_iff_two_dvd] at h
        · apply dvd_mul_of_dvd_right
          simp at h
          rw [← even_iff_two_dvd]
          apply Odd.sub_odd h
          use 998
          simp
      rwa [sub_add_eq_sub_sub]
    -- Then $2|P(n)$ so $2|Q(P(n))-c=1-c$ and so $c$ is odd.
    have h3 : Odd c := by
      -- $2|Q(P(n))-c=1-c$
      have h3' : 2 ∣ 1 - c := by
        rw [Polynomial.eval_eq_sum_range, Finset.sum_range_eq_add_Ico _ (by omega)] at hn
        simp at hn
        have : 1 - c = ∑ x ∈ Finset.Ico 1 (Q.natDegree + 1), Q.coeff x * eval n P ^ x := by
          simp [← hn, c]
        rw [this]
        apply Finset.dvd_sum
        intro x hx
        apply dvd_mul_of_dvd_right
        apply dvd_pow (h2 n)
        simp at hx
        linarith
      rw [← Int.not_even_iff_odd, ← Int.even_sub_one, ← even_neg, even_iff_two_dvd]
      simp [h3']
    -- Hence $Q(2x)$ is odd since we have all terms even apart from the odd constant term $c$.
    have h4 : ∀ x : ℤ, Odd (Q.eval (2 * x)) := by
      intro x
      suffices Even (Q.eval (2 * x) - c) by
        have := Even.add_odd this h3
        rwa [sub_add_cancel] at this
      rw [even_iff_two_dvd, Polynomial.eval_eq_sum_range, Finset.sum_range_eq_add_Ico _ (by omega)]
      simp [c]
      apply Finset.dvd_sum
      intro y hy
      apply dvd_mul_of_dvd_right
      simp at hy
      apply dvd_pow _ (by linarith)
      simp
    -- But this contradicts $Q(1998)=2000$. Hence no $n$ exists.
    specialize h4 999
    simp [hQ] at h4
    tauto
