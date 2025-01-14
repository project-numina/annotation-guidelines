import Mathlib


/- The positive integers a and b are such that the numbers (15a + 16b) and (16a - 15b) are both squares of positive integers.
What is the least possible value that can be taken on by the smaller of these two squares?-/
theorem number_theory_9019:
  IsLeast {x : ℕ | ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ x = min (15 * a + 16 * b) (16 * a - 15 * b) ∧
  IsSquare (15 * a + 16 * b) ∧ IsSquare (16 * a - 15 * b) ∧
  0 < (15 * a + 16 * b) ∧ 0 < (16 * a - 15 * b)} (481 ^ 2) := by
  constructor
  . simp
    -- To show that 481 ^ 2 is admissable, it is sufficient to take `a = 31 * 481` and `b = 481`
    refine ⟨31 * 481, by norm_num, 481, by norm_num, ?_⟩
    norm_num
    use 481
  . rintro z ⟨a, b, ha, hb, h⟩
    -- -- Let 15a + 16b = x^2 and 16a - 15b = y^2
    obtain ⟨x, hx⟩ := h.2.1
    obtain ⟨y, hy⟩ := h.2.2.1
    -- Then we obtain x^4 + y^4 = (15a + 16b)^2 + (16a - 15b)^2 = (15^2 + 16^2)(a^2 + b^2) = 481(a^2 + b^2)
    have hxy : x^4 + y^4 = 481 * (a^2 + b^2) := by nlinarith [hx, hy]
    -- In particular, 481 = 13 * 37 ∣ x^4 + y^4
    have hdiv : 13 * 37 ∣ x^4 + y^4 := by
      rw [hxy]
      exact dvd_mul_right 481 (a^2 + b^2)
    -- From this we can conclude that 13 ∣ x, y
    have h13 : 13 ∣ x ∧ 13 ∣ y := by
      -- Observe that x ^ 4 + y ^ 4 = 0 (mod 13)
      have hxy13 : (x^4 + y^4) % 13 = 0 := by
        rw [hxy]
        omega
      -- Assume for contradiction that 13 ∣ x and 13 ∣ y is false
      by_contra h
      replace h : (¬ 13 ∣ x) ∨ (¬ 13 ∣ y) := by omega
      cases' h with hx hy
      · -- Obtain k : ℤ such that k * x % 13 = 1
        have : x.natAbs.Coprime 13 := by
          convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 13) (by norm_num) _
          contrapose! hx
          exact Int.natAbs_dvd_natAbs.mp hx
        obtain ⟨k, hk⟩ := Int.mod_coprime (a := x.natAbs) (b := 13) this
        -- Then (y * k) ^ 4 = -1 (mod 13)
        have : (y * k) ^ 4 % 13 = -1 % 13 := by
          replace hk : (↑x.natAbs * k) ^ 4 ≡ 1 [ZMOD ↑13] := by convert Int.ModEq.pow 4 hk
          replace hk : x ^ 4 * k ^ 4 ≡ 1 [ZMOD ↑13] := by
            convert hk
            rw [mul_pow, show ((x.natAbs : ℤ) ^ 4 = (↑x.natAbs ^ 2) ^ 2) by ring, Int.natAbs_pow_two]
            ring
          replace hk := Int.ModEq.eq hk
          replace hxy13 : x ^ 4 % 13 = - y ^ 4 % 13 := by omega
          rw [Int.mul_emod, hxy13] at hk
          simp only [Int.reduceMod] at hk
          rw [mul_pow, Int.mul_emod, ← hk, Int.emod_eq_emod_iff_emod_sub_eq_zero]
          rw [sub_neg_eq_add, Int.add_emod_emod, EuclideanDomain.mod_eq_zero, ← add_mul, Int.neg_emod, Int.sub_emod]
          apply dvd_mul_of_dvd_left
          rw [Int.emod_def, Int.emod_def]
          simp
          ring_nf
          norm_num
        -- It follows that (y * k) ^ 12 = -1 (mod 13)
        have : (y * k) ^ 12 % 13 = -1 % 13 := by
          change (y * k) ^ (4 * 3) % 13 = -1 % 13
          rw [pow_mul, Int.ModEq.eq (Int.ModEq.pow 3 this)]
          simp
        -- For the next statement, we will use that (y * k) is coprime with 13
        have hcop : IsCoprime (y * k) 13 := by
          rw [Int.coprime_iff_nat_coprime]
          simp only [Int.reduceAbs]
          rw [Int.natAbs_mul]
          apply Nat.Coprime.mul
          · convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 13) (by norm_num) _
            intro hy13
            replace hy13 : 13 ∣ y := by omega
            apply hx
            replace hxy13 : 13 ∣ x ^ 4 + y ^ 4 := by aesop
            rw [dvd_add_left (dvd_pow hy13 (show 4 ≠ 0 by norm_num))] at hxy13
            apply Int.Prime.dvd_pow' (by norm_num) hxy13
          . convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 13) (by norm_num) _
            intro hk13
            replace hk13 : k % 13 = 0 := by omega
            replace hk := Int.ModEq.eq hk
            simp only [Int.natCast_natAbs, Nat.cast_ofNat, Int.reduceMod] at hk
            rw [Int.mul_emod, hk13] at hk
            aesop
        -- But this contradicts Fermat's Little Theorem on (y * k)
        have := Int.ModEq.eq (Int.ModEq.pow_card_sub_one_eq_one (show Nat.Prime 13 by norm_num) hcop)
        aesop
      · -- Carry out an analogous proof to the case above
        -- Obtain k : ℤ such that k * y % 13 = 1
        have : y.natAbs.Coprime 13 := by
          convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 13) (by norm_num) _
          contrapose! hy
          exact Int.natAbs_dvd_natAbs.mp hy
        obtain ⟨k, hk⟩ := Int.mod_coprime (a := y.natAbs) (b := 13) this
        -- Then (y * k) ^ 4 = -1 (mod 13)
        have : (x * k) ^ 4 % 13 = -1 % 13 := by
          replace hk : (↑y.natAbs * k) ^ 4 ≡ 1 [ZMOD ↑13] := by convert Int.ModEq.pow 4 hk
          replace hk : y ^ 4 * k ^ 4 ≡ 1 [ZMOD ↑13] := by
            convert hk
            rw [mul_pow, show ((y.natAbs : ℤ) ^ 4 = (↑y.natAbs ^ 2) ^ 2) by ring, Int.natAbs_pow_two]
            ring
          replace hk := Int.ModEq.eq hk
          replace hxy13 : y ^ 4 % 13 = - x ^ 4 % 13 := by omega
          rw [Int.mul_emod, hxy13] at hk
          simp only [Int.reduceMod] at hk
          rw [mul_pow, Int.mul_emod, ← hk, Int.emod_eq_emod_iff_emod_sub_eq_zero]
          rw [sub_neg_eq_add, Int.add_emod_emod, EuclideanDomain.mod_eq_zero, ← add_mul, Int.neg_emod, Int.sub_emod]
          apply dvd_mul_of_dvd_left
          rw [Int.emod_def, Int.emod_def]
          simp
          ring_nf
          norm_num
        -- It follows that (y * k) ^ 12 = -1 (mod 13)
        have : (x * k) ^ 12 % 13 = -1 % 13 := by
          change (x * k) ^ (4 * 3) % 13 = -1 % 13
          rw [pow_mul, Int.ModEq.eq (Int.ModEq.pow 3 this)]
          simp
        -- For the next statement, we will use that (y * k) is coprime with 13
        have hcop : IsCoprime (x * k) 13 := by
          rw [Int.coprime_iff_nat_coprime]
          simp only [Int.reduceAbs]
          rw [Int.natAbs_mul]
          apply Nat.Coprime.mul
          · convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 13) (by norm_num) _
            intro hy13
            replace hy13 : 13 ∣ x := by omega
            apply hy
            replace hxy13 : 13 ∣ x ^ 4 + y ^ 4 := by aesop
            rw [dvd_add_right (dvd_pow hy13 (show 4 ≠ 0 by norm_num))] at hxy13
            apply Int.Prime.dvd_pow' (by norm_num) hxy13
          . convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 13) (by norm_num) _
            intro hk13
            replace hk13 : k % 13 = 0 := by omega
            replace hk := Int.ModEq.eq hk
            simp only [Int.natCast_natAbs, Nat.cast_ofNat, Int.reduceMod] at hk
            rw [Int.mul_emod, hk13] at hk
            aesop
        -- But this contradicts Fermat's Little Theorem on (y * k)
        have := Int.ModEq.eq (Int.ModEq.pow_card_sub_one_eq_one (show Nat.Prime 13 by norm_num) hcop)
        aesop
    -- Analogously, have that and 37 ∣ x, y
    have h37 : 37 ∣ x ∧ 37 ∣ y := by
      -- Observe that x ^ 4 + y ^ 4 = 0 (mod 37)
      have hxy37 : (x^4 + y^4) % 37 = 0 := by
        rw [hxy]
        omega
      -- Assume for contradiction that 37 ∣ x and 37 ∣ y is false
      by_contra h
      replace h : (¬ 37 ∣ x) ∨ (¬ 37 ∣ y) := by omega
      cases' h with hx hy
      · -- Obtain k : ℤ such that k * x % 37 = 1
        have : x.natAbs.Coprime 37 := by
          convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 37) (by norm_num) _
          contrapose! hx
          exact Int.natAbs_dvd_natAbs.mp hx
        obtain ⟨k, hk⟩ := Int.mod_coprime (a := x.natAbs) (b := 37) this
        -- Then (y * k) ^ 4 = -1 (mod 37)
        have : (y * k) ^ 4 % 37 = -1 % 37 := by
          replace hk : (↑x.natAbs * k) ^ 4 ≡ 1 [ZMOD ↑37] := by convert Int.ModEq.pow 4 hk
          replace hk : x ^ 4 * k ^ 4 ≡ 1 [ZMOD ↑37] := by
            convert hk
            rw [mul_pow, show ((x.natAbs : ℤ) ^ 4 = (↑x.natAbs ^ 2) ^ 2) by ring, Int.natAbs_pow_two]
            ring
          replace hk := Int.ModEq.eq hk
          replace hxy37 : x ^ 4 % 37 = - y ^ 4 % 37 := by omega
          rw [Int.mul_emod, hxy37] at hk
          simp only [Int.reduceMod] at hk
          rw [mul_pow, Int.mul_emod, ← hk, Int.emod_eq_emod_iff_emod_sub_eq_zero]
          rw [sub_neg_eq_add, Int.add_emod_emod, EuclideanDomain.mod_eq_zero, ← add_mul, Int.neg_emod, Int.sub_emod]
          apply dvd_mul_of_dvd_left
          rw [Int.emod_def, Int.emod_def]
          simp
          ring_nf
          norm_num
        -- It follows that (y * k) ^ 36 = -1 (mod 37)
        have : (y * k) ^ 36 % 37 = -1 % 37 := by
          change (y * k) ^ (4 * 9) % 37 = -1 % 37
          rw [pow_mul, Int.ModEq.eq (Int.ModEq.pow 9 this)]
          simp
        -- For the next statement, we will use that (y * k) is coprime with 37
        have hcop : IsCoprime (y * k) 37 := by
          rw [Int.coprime_iff_nat_coprime]
          simp only [Int.reduceAbs]
          rw [Int.natAbs_mul]
          apply Nat.Coprime.mul
          · convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 37) (by norm_num) _
            intro hy37
            replace hy37 : 37 ∣ y := by omega
            apply hx
            replace hxy37 : 37 ∣ x ^ 4 + y ^ 4 := by aesop
            rw [dvd_add_left (dvd_pow hy37 (show 4 ≠ 0 by norm_num))] at hxy37
            apply Int.Prime.dvd_pow' (by norm_num) hxy37
          . convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 37) (by norm_num) _
            intro hk37
            replace hk37 : k % 37 = 0 := by omega
            replace hk := Int.ModEq.eq hk
            simp only [Int.natCast_natAbs, Nat.cast_ofNat, Int.reduceMod] at hk
            rw [Int.mul_emod, hk37] at hk
            aesop
        -- But this contradicts Fermat's Little Theorem on (y * k)
        have := Int.ModEq.eq (Int.ModEq.pow_card_sub_one_eq_one (show Nat.Prime 37 by norm_num) hcop)
        aesop
      · -- Carry out an analogous proof to the case above
        -- Obtain k : ℤ such that k * y % 37 = 1
        have : y.natAbs.Coprime 37 := by
          convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 37) (by norm_num) _
          contrapose! hy
          exact Int.natAbs_dvd_natAbs.mp hy
        obtain ⟨k, hk⟩ := Int.mod_coprime (a := y.natAbs) (b := 37) this
        -- Then (y * k) ^ 4 = -1 (mod 37)
        have : (x * k) ^ 4 % 37 = -1 % 37 := by
          replace hk : (↑y.natAbs * k) ^ 4 ≡ 1 [ZMOD ↑37] := by convert Int.ModEq.pow 4 hk
          replace hk : y ^ 4 * k ^ 4 ≡ 1 [ZMOD ↑37] := by
            convert hk
            rw [mul_pow, show ((y.natAbs : ℤ) ^ 4 = (↑y.natAbs ^ 2) ^ 2) by ring, Int.natAbs_pow_two]
            ring
          replace hk := Int.ModEq.eq hk
          replace hxy37 : y ^ 4 % 37 = - x ^ 4 % 37 := by omega
          rw [Int.mul_emod, hxy37] at hk
          simp only [Int.reduceMod] at hk
          rw [mul_pow, Int.mul_emod, ← hk, Int.emod_eq_emod_iff_emod_sub_eq_zero]
          rw [sub_neg_eq_add, Int.add_emod_emod, EuclideanDomain.mod_eq_zero, ← add_mul, Int.neg_emod, Int.sub_emod]
          apply dvd_mul_of_dvd_left
          rw [Int.emod_def, Int.emod_def]
          simp
          ring_nf
          norm_num
        -- It follows that (y * k) ^ 36 = -1 (mod 37)
        have : (x * k) ^ 36 % 37 = -1 % 37 := by
          change (x * k) ^ (4 * 9) % 37 = -1 % 37
          rw [pow_mul, Int.ModEq.eq (Int.ModEq.pow 9 this)]
          simp
        -- For the next statement, we will use that (y * k) is coprime with 37
        have hcop : IsCoprime (x * k) 37 := by
          rw [Int.coprime_iff_nat_coprime]
          simp only [Int.reduceAbs]
          rw [Int.natAbs_mul]
          apply Nat.Coprime.mul
          · convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 37) (by norm_num) _
            intro hy37
            replace hy37 : 37 ∣ x := by omega
            apply hy
            replace hxy37 : 37 ∣ x ^ 4 + y ^ 4 := by aesop
            rw [dvd_add_right (dvd_pow hy37 (show 4 ≠ 0 by norm_num))] at hxy37
            apply Int.Prime.dvd_pow' (by norm_num) hxy37
          . convert Nat.Prime.coprime_pow_of_not_dvd (m := 1) (p := 37) (by norm_num) _
            intro hk37
            replace hk37 : k % 37 = 0 := by omega
            replace hk := Int.ModEq.eq hk
            simp only [Int.natCast_natAbs, Nat.cast_ofNat, Int.reduceMod] at hk
            rw [Int.mul_emod, hk37] at hk
            aesop
        -- But this contradicts Fermat's Little Theorem on (y * k)
        have := Int.ModEq.eq (Int.ModEq.pow_card_sub_one_eq_one (show Nat.Prime 37 by norm_num) hcop)
        aesop
    -- Hence x and y are divisible by 481
    have h481 : 481 ∣ x ∧ 481 ∣ y := by
      constructor
      · omega
      · omega
    -- To finish the proof, it will suffice that any minimal `z` square satisfying the conditions is divisible by 481 ^ 2
    suffices : 481 ^ 2 ∣ (z : ℤ)
    · have hzpos : 0 < (z : ℤ) := by aesop
      replace this := Int.le_of_dvd hzpos this
      exact Int.ofNat_le.mp this
    rw [h.1, hx, hy]
    -- Split the remaining proof into two cases based on whether `x * x` or `y * y` is smaller and finish using `h481`
    wlog hxy : x * x ≤ y * y
    · simp at hxy
      rw [min_eq_right_of_lt hxy, pow_two]
      exact mul_dvd_mul h481.2 h481.2
    . rw [min_eq_left hxy, pow_two]
      exact mul_dvd_mul h481.1 h481.1
