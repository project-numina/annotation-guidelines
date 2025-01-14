import Mathlib

/- This file contains a formalization of a solution fitting the guidelines laid out in the README.
  In particular, pay particular attention to comments on lines `14`, `20`
  detailing appropriate lemmas to be left as `sorry`-/

/-- Let $a$ and $b$ be two positive integers. Prove that the integer  $$ a^{2}+\left\lceil\frac{4 a^{2}}{b}\right\rceil $$  is not a square. (Here $\lceil z\rceil$ denotes the least integer greater than or equal to z.) (Russia) -/
theorem number_theory_23923 {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    ¬IsSquare (a ^ 2 + ⌈(4 * a ^ 2 / b : ℚ)⌉) := by
  -- Arguing indirectly, assume that $$ a^{2}+\left\lceil\frac{4 a^{2}}{b}\right\rceil=(a+k)^{2}, \quad \text { or } \quad\left\lceil\frac{(2 a)^{2}}{b}\right\rceil=(2 a+k) k $$
  by_contra h
  obtain ⟨k', h⟩ := h
  wlog k_pos : 0 ≤ k'
  . -- `comment` : The following line may be left as a `sorry`
    sorry
  generalize hk' : k' - a = k
  rw [sub_eq_iff_eq_add'] at hk'
  subst hk'
  -- `comment` : another sub-lemma that may be left as a `sorry`
  have h' : ⌈((2 * a : ℤ) ^ 2 / b : ℚ)⌉ = ((2 * a : ℤ) + k) * k := by sorry
  -- Clearly, $k \geqslant 1$.
  have hk1 : 1 ≤ k := by
    by_contra! hk1
    have : ⌈((2 * a : ℤ) ^ 2 / b : ℚ)⌉ > 0 := by positivity
    have : ((2 * a : ℤ) + k) * k < 0 := by nlinarith
    linarith
  lift k to ℕ using by omega
  -- In other words, the equation  $$ \left\lceil\frac{c^{2}}{b}\right\rceil=(c+k) k $$  has a positive integer solution $(c, k)$, with an even value of $c$. Choose a positive integer solution of (1) with minimal possible value of $k$, without regard to the parity of $c$.
  have exists_k : ∃ k : ℕ, ∃ c : ℤ, 0 < c ∧ ⌈(c ^ 2 / b : ℚ)⌉ = (c + k) * k :=
    ⟨k, 2 * a, by positivity, by simpa using h'⟩
  classical
    let k := Nat.find exists_k
    have hk : ∃ c : ℤ, 0 < c ∧ ⌈(c ^ 2 / b : ℚ)⌉ = (c + k) * k := Nat.find_spec exists_k
    have k_min {m : ℕ} (hm : m < k) : ¬∃ c : ℤ, 0 < c ∧ ⌈(c ^ 2 / b : ℚ)⌉ = (c + m) * m :=
      Nat.find_min exists_k hm
  choose c hc0 hk using hk
  have hk1 : 1 ≤ k := by
    by_contra! hk1
    have : ⌈(c ^ 2 / b : ℚ)⌉ > 0 := by positivity
    have : (c + k) * k < 0 := by nlinarith
    linarith
  -- From  $$ \frac{c^{2}}{b}>\left\lceil\frac{c^{2}}{b}\right\rceil-1=c k+k^{2}-1 \geqslant c k $$
  have h0r : c * k < (c ^ 2 / b : ℚ) :=
    calc
      _ ≤ (c * k + k ^ 2 - 1 : ℚ) := by
        norm_cast
        rw [add_sub_assoc, le_add_iff_nonneg_right]
        simpa
      _ = ⌈(c ^ 2 / b : ℚ)⌉ - 1 := by rw [hk]; push_cast; ring
      _ < _ := by linarith [Int.ceil_lt_add_one (c ^ 2 / b : ℚ)]
  rw [lt_div_iff (by positivity)] at h0r
  norm_cast at h0r
  rw [pow_two, mul_assoc, mul_lt_mul_left hc0] at h0r
  -- and  $$ \frac{(c-k)(c+k)}{b}<\frac{c^{2}}{b} \leqslant\left\lceil\frac{c^{2}}{b}\right\rceil=(c+k) k $$
  have hrk : ((c - k) * (c + k) / b : ℚ) < (c + k) * k :=
    calc
      _ < (c ^ 2 / b : ℚ) := by gcongr; ring_nf; simp; positivity
      _ ≤ ⌈(c ^ 2 / b : ℚ)⌉ := Int.le_ceil _
      _ = _ := by simp [hk]
  rw [div_lt_iff (by positivity)] at hrk
  norm_cast at hrk
  rw [mul_assoc, mul_comm, mul_lt_mul_left (by positivity)] at hrk
  -- it can be seen that $c>b k>c-k$, so  $$ c=k b+r \quad \text { with some } 0< r< k $$
  generalize hc : c - k * b = r
  rw [sub_eq_iff_eq_add] at hc
  -- By substituting this in (1) we get  $$ \left\lceil\frac{c^{2}}{b}\right\rceil=\left\lceil\frac{(b k+r)^{2}}{b}\right\rceil=k^{2} b+2 k r+\left\lceil\frac{r^{2}}{b}\right\rceil $$  and  $$ (c+k) k=(k b+r+k) k=k^{2} b+2 k r+k(k-r) $$  so  $$ \left\lceil\frac{r^{2}}{b}\right\rceil=k(k-r) $$
  subst hc
  simp at h0r
  lift r to ℕ using h0r.le
  norm_cast at h0r
  simp [sub_lt_iff_lt_add'] at hrk
  push_cast at hk
  ring_nf at hk
  rw [pow_two (b : ℚ), ← mul_assoc, mul_inv_cancel_right₀ (by positivity), mul_inv_cancel_right₀ (by positivity), add_right_comm, add_comm] at hk
  norm_cast at hk
  rw [Int.ceil_add_int, ← eq_sub_iff_add_eq] at hk
  push_cast at hk
  replace hk : ⌈(r ^ 2 / b : ℚ)⌉ = k * (k - r) := by
    convert hk using 1
    ring
  -- Notice that relation (2) provides another positive integer solution of (1), namely $c^{\prime}=r$ and $k^{\prime}=k-r$, with $c^{\prime}>0$ and $0< k^{\prime}< k$. That contradicts the minimality of $k$, and hence finishes the solution.
  refine k_min (by omega : k - r < k) ⟨r, by omega, ?_⟩
  simp [hk]
  rw [Nat.cast_sub (by omega)]
  ring
