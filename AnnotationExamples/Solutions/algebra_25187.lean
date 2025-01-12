import Mathlib

open Real

/- This file contains a formalization of a solution fitting the guidelines laid out in the README.
  In particular, pay particular attention to comments on lines `46`, `99` and `165`
  detailing appropriate lemmas to be left as `sorry`-/


/- Let $a, b, c>0$ and $a b+b c+c a=1$. Prove the inequality  $$ \sqrt[3]{\frac{1}{a}+6 b}+\sqrt[3]{\frac{1}{b}+6 c}+\sqrt[3]{\frac{1}{c}+6 a} \leq \frac{1}{a b c} $$ -/
theorem algebra_25187
    (a b c : ℝ)
    (h_apos : 0 < a)
    (h_bpos : 0 < b)
    (h_cpos : 0 < c)
    (h₀ : a * b + b * c + c * a = 1) :
    (1 / a + 6 * b) ^ ((3 : ℝ)⁻¹) + (1 / b + 6 * c) ^ ((3 : ℝ)⁻¹) + (1 / c + 6 * a) ^ ((3 : ℝ)⁻¹) ≤ 1 / (a * b * c) := by

  -- General mean inequality $\left(M_{1} \leq M_{3}\right)$, via Hölder’s inequality
  have l_m1_le_m3
      {a b c : ℝ}
      (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
      (a + b + c) / 3 ≤ ((a ^ 3 + b ^ 3 + c ^ 3) / 3) ^ (1 / (3 : ℝ)) := by

    let f : ℕ → ℝ := fun x => match x with
    | 0 => a
    | 1 => b
    | 2 => c
    | _ => 0
    let g : ℕ → ℝ := fun _ => 3⁻¹
    let p : ℝ := 3
    let q : ℝ := 3 / 2
    have h_pq_conjexp : p.IsConjExponent q := by
      refine (isConjExponent_iff _ _).mpr ?_
      constructor <;> norm_num

    have h_holder := inner_le_Lp_mul_Lq {0, 1, 2} f g h_pq_conjexp
    simp [f, g, abs_of_pos, ha, hb, hc, p, q] at h_holder
    convert h_holder using 1
    . ring_nf
    . conv => lhs; rw [div_eq_mul_inv, mul_rpow (by linarith [pow_pos ha 3, pow_pos hb 3, pow_pos hc 3]) (by norm_num)]
      conv => rhs; rw [mul_rpow zero_le_three (le_of_lt (rpow_pos_of_pos (by norm_num) _))]
      congr 1
      . simp only [← rpow_natCast, Nat.cast_ofNat, one_div, ← add_assoc]
      . have t0 : 0 < (3 : ℝ)⁻¹ := by norm_num
      -- `comment` : here is an appropriate tedious lemma that may be left as a `sorry`
        have t1 : (0 : ℝ) < 3 ^ (2 / 3 : ℝ) * (3⁻¹ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by sorry
        have t2 : ((3 : ℝ)⁻¹ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≠ 0 := by
          apply ne_of_gt (rpow_pos_of_pos _ _)
          apply rpow_pos_of_pos t0
        apply (logb_eq_iff_rpow_eq (show 0 < (3 : ℝ)⁻¹ by norm_num) (show (3 : ℝ)⁻¹ ≠ 1 by norm_num) t1).mp
        rw [logb, log_mul (by norm_num) t2, log_rpow zero_lt_three,
            log_rpow (rpow_pos_of_pos t0 (3 / 2)), log_rpow t0, log_inv]
        ring_nf
        field_simp

  -- By general mean inequality $\left(M_{1} \leq M_{3}\right)$, the LHS of the inequality to be proved does not exceed  $$ E=\frac{3}{\sqrt[3]{3}} \sqrt[3]{\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+6(a+b+c)} $$
  let E : ℝ := 3 / (3 ^ ((3 : ℝ)⁻¹)) * (1 / a + 1 / b + 1 / c + 6 * (a + b + c)) ^ ((3 : ℝ)⁻¹)
  have r1 : (1 / a + 6 * b) ^ ((3 : ℝ)⁻¹) + (1 / b + 6 * c) ^ ((3 : ℝ)⁻¹) + (1 / c + 6 * a) ^ ((3 : ℝ)⁻¹) ≤ E := by
    have tmph {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < (1 / x + 6 * y) ∧ 0 < (1 / x + 6 * y) ^ ((3 : ℝ)⁻¹) := by
      have : 0 < (1 / x + 6 * y) := add_pos (one_div_pos.mpr hx) (mul_pos (by norm_num) hy)
      exact ⟨this, rpow_pos_of_pos this 3⁻¹⟩
    have ⟨h1, h1'⟩ := tmph h_apos h_bpos
    have ⟨h2, h2'⟩ := tmph h_bpos h_cpos
    have ⟨h3, h3'⟩ := tmph h_cpos h_apos
    specialize l_m1_le_m3 h1' h2' h3'
    convert mul_le_mul_of_nonneg_right l_m1_le_m3 zero_le_three using 1
    . ring_nf
    . simp only [E, ← rpow_natCast, Nat.cast_ofNat]
      rw [rpow_inv_rpow (le_of_lt h1) three_ne_zero,
          rpow_inv_rpow (le_of_lt h2) three_ne_zero,
          rpow_inv_rpow (le_of_lt h3) three_ne_zero,
          div_eq_mul_inv, mul_assoc, mul_comm, ← inv_rpow zero_le_three,
          ← mul_rpow (show 0 ≤ (3:ℝ)⁻¹ by norm_num) (by linarith only [h1, h2, h3]),
          mul_comm 3⁻¹, ← div_eq_mul_inv]
      ring_nf

  -- From $a b+b c+c a=1$ we obtain that $3 a b c(a+b+c)=3(a b \cdot a c+$ $a b \cdot b c+a c \cdot b c) \leq(a b+a c+b c)^{2}=1$; hence $6(a+b+c) \leq \frac{2}{a b c}$.
  have r2 : 6 * (a + b + c) ≤ 2 / (a * b * c) := by
    have hpos : 0 < a * b * c := mul_pos (mul_pos h_apos h_bpos) h_cpos
    have : 3 * a * b * c * (a + b + c) ≤ (a * b + b * c + c * a) ^ 2 := by
      apply sub_nonneg.mp
      trans ((a * b - a * c) ^ 2 + (a * b - b * c) ^ 2 + (a * c - b * c) ^ 2) / 2
      . apply div_nonneg ?_ zero_le_two
        simp only [add_nonneg, sq_nonneg]
      . apply le_of_eq
        ring_nf
    rw [h₀, one_pow, show 3 * a * b * c = 3 * (a * b * c) by ring_nf] at this
    apply (div_le_div_right hpos).mpr at this
    rw [mul_assoc, mul_div_assoc, mul_div_cancel_left₀ _ ((ne_of_lt hpos).symm)] at this
    apply (div_le_div_right (show (0 : ℝ) < 2 by norm_num)).mp
    convert this using 1 <;> ring_nf

  -- Since $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}=\frac{a b+b c+c a}{a b c}=\frac{1}{a b c}$, it follows that  $$ E \leq \frac{3}{\sqrt[3]{3}} \sqrt[3]{\frac{3}{a b c}} $$
  have r3 : E ≤ 3 / (3 ^ ((3 : ℝ)⁻¹)) * (3 / (a * b * c)) ^ ((3 : ℝ)⁻¹) := by
    have hpos : (0 : ℝ) < 3 / (3 ^ ((3 : ℝ)⁻¹)) := by
      refine div_pos three_pos ?_
      exact rpow_pos_of_pos three_pos _
    -- `comment` : here is another appropriate tedious lemma that may be left as a `sorry`
    have hnonneg : 0 ≤ 1 / (a * b * c) + 6 * (a + b + c) := by sorry
    have : 1 / a + 1 / b + 1 / c = 1 / (a * b * c) := by
      field_simp
      rw [add_mul]
      linarith only [h₀]
    dsimp [E]
    apply (div_le_div_right hpos).mp
    simp_rw [mul_div_cancel_left₀ _ (ne_of_gt hpos), this]
    refine rpow_le_rpow hnonneg ?_ (by norm_num)
    trans 1 / (a * b * c) + 2 / (a * b * c)
    . linarith only [r2]
    . rw [← add_div]
      norm_num

  -- $$ \frac{3}{\sqrt[3]{3}} \sqrt[3]{\frac{3}{a b c}} \leq \frac{1}{a b c} $$
  have r4 : 3 / (3 ^ ((3 : ℝ)⁻¹)) * (3 / (a * b * c)) ^ ((3 : ℝ)⁻¹) ≤ 1 / (a * b * c) := by
    rw [div_eq_mul_one_div 3 (a * b * c)]
    set t := 1 / (a * b * c)
    have htpos : 0 < t := by
      dsimp [t]
      apply one_div_pos.mpr
      exact mul_pos (mul_pos h_apos h_bpos) h_cpos

    -- from the AM-GM inequality $1=a b+b c+$ $c a \geq 3 \sqrt[3]{(a b c)^{2}}$
    have ramgm: 3 * ((a * b * c) ^ 2) ^ ((3 : ℝ)⁻¹) ≤ a * b + b * c + c * a := by
      have hw : 0 ≤ (3 : ℝ)⁻¹ := by norm_num
      have hz1 : 0 ≤ a * b := le_of_lt (mul_pos h_apos h_bpos)
      have hz2 : 0 ≤ b * c := le_of_lt (mul_pos h_bpos h_cpos)
      have hz3 : 0 ≤ c * a := le_of_lt (mul_pos h_cpos h_apos)
      have := geom_mean_le_arith_mean3_weighted hw hw hw hz1 hz2 hz3 (by norm_num)
      apply (mul_le_mul_left zero_lt_three).mpr at this
      rw [← mul_rpow hz1 hz2, ← mul_rpow (mul_nonneg hz1 hz2) hz3] at this
      convert this using 1 <;> ring_nf

    -- by ramgm, together with $ab + bc + ca = 1$, we have $3 \sqrt{3} \le \frac{1}{abc}$.
    have htge : 3 * √ 3 ≤ t := by
      have hnonneg : 0 ≤ 3 * ((a * b * c) ^ 2) ^ ((3 : ℝ)⁻¹) := by
        refine mul_nonneg zero_le_three ?_
        exact rpow_nonneg (sq_nonneg _) _
      rw [h₀] at ramgm
      have := (rpow_le_rpow_iff hnonneg zero_le_one zero_lt_three).mpr ramgm
      rw [mul_rpow zero_le_three (rpow_nonneg (sq_nonneg _) _),
          ← rpow_mul (sq_nonneg _),
          one_rpow, inv_mul_cancel₀ three_ne_zero, rpow_one] at this
      rw [← abs_of_pos (show 0 < 3 * √ 3 by norm_num), ← abs_of_pos htpos]
      apply sq_le_sq.mp
      simp_rw [mul_pow, sq_sqrt zero_le_three, ← pow_succ, two_add_one_eq_three, t, div_pow, one_pow]
      apply (le_div_iff₀ (pow_pos (mul_pos (mul_pos h_apos h_bpos) h_cpos) _)).mpr
      convert this
      norm_num

    -- The desired inequality now follows.
    apply (div_le_div_right htpos).mp
    rw [mul_rpow (zero_le_three) (le_of_lt htpos),
        div_eq_mul_inv, ← rpow_neg_one t, mul_assoc, mul_assoc, ← rpow_add htpos, ← mul_assoc,
        div_self (ne_of_lt htpos).symm]
    field_simp
    trans 3 * (3 * √ 3) ^ ((1 + -3) / 3 : ℝ)
    -- 3 * t ^ ((1 + -3) / 3) ≤ 3 * (3 * √3) ^ ((1 + -3) / 3)
    . have hpos : 0 < 3 * √3 := by norm_num
      have hneg : ((1 + -3) / 3 : ℝ) < 0 := by norm_num
      apply (mul_le_mul_left (zero_lt_three)).mpr
      exact (rpow_le_rpow_iff_of_neg htpos hpos hneg).mpr htge
    -- 3 * (3 * √3) ^ ((1 + -3) / 3) ≤ 1, actually the equality holds
    . --`comment` : yet another appropriate tedious lemma that may be left as a `sorry`
      have hpos : 0 < 3 * (3 * √3) ^ ((1 + -3) / 3 : ℝ) := by sorry
      apply (log_le_log_iff hpos (zero_lt_one)).mp
      apply le_of_eq
      rw [log_mul three_ne_zero (by linarith only [hpos]),
          log_rpow (by norm_num),
          log_mul three_ne_zero (by norm_num), log_sqrt zero_le_three,
          log_one]
      ring_nf

  linarith only [r1, r3, r4]
