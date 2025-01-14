import Mathlib

/-
N2. For each prime $p$, there is a kingdom of $p$-Landia consisting of $p$ islands numbered $1,2, \ldots, p$. Two distinct islands numbered $n$ and $m$ are connected by a bridge if and only if $p$ divides $\left(n^{2}-m+1\right)\left(m^{2}-n+1\right)$. The bridges may pass over each other, but cannot cross. Prove that for infinitely many $p$ there are two islands in $p$-Landia not connected by a chain of bridges.
(Denmark)
-/
theorem imo_2020_sl_n2 :
    let G p : SimpleGraph (ZMod p) := .fromRel fun m n ↦ (n^2 - m + 1) * (m^2 - n + 1) = 0;
    Set.Infinite {p : ℕ | p.Prime ∧ ¬ (G p).Connected} := by
  classical
  intro G
  -- We prove that for each prime $p>3$ dividing a number of the form $x^{2}-x+1$ with integer $x$ there are two unconnected islands in $p$-Landia.
  have h : ∀ (p : ℕ), p.Prime → (3 < p) → (∃ (x : ZMod p), x^2 - x + 1 = 0) → ¬ (G p).Connected := by
    intro p h_prime hp ⟨x, hx⟩
    -- Provide an auxilary `NeZero p` instance for further proof. For example it helps Lean to understand that `ZMod p`, and thus `G` are finite.
    have _ : NeZero p := by
      constructor
      linarith
    -- Prove `NoZeroDivisors` to be able to show `(n^2 - m + 1) * (m^2 - n + 1) = 0` iff one of the multipliers is zero.
    have _ : NoZeroDivisors (ZMod p) := by
      have := @ZMod.instIsDomain p ⟨h_prime⟩
      infer_instance
    -- A bridge connects $m$ and $n$ if $n \equiv m^{2}+1(\bmod p)$ or $m \equiv n^{2}+1(\bmod p)$.
    have h1 : ∀ m n, m ≠ n → (n = m^2 + 1 ∨ m = n^2 + 1) → (G p).Adj m n := by
      intro m n h_neq h
      simp [G, h_neq]
      left
      rcases h with (h | h) <;> simp [h]
    -- If $m^{2}+1 \equiv n$ $(\bmod p)$, we draw an arrow starting at $m$ on the bridge connecting $m$ and $n$.
    let arrows : Digraph (ZMod p) := ⟨fun m n ↦ m ≠ n ∧ m^2 + 1 = n⟩
    -- Clearly only one arrow starts at $m$ if $m^{2}+1 \not \equiv m(\bmod p)$,
    have h2 : ∀ m, m^2 + 1 ≠ m → ∀ n, arrows.Adj m n ↔ n = m^2 + 1 := by
      intro m hm n
      simp [arrows]
      constructor
      · intro h
        exact h.right.symm
      · intro h
        subst h
        simp [hm.symm]
    -- and no arrows otherwise.
    have h3 : ∀ m, m^2 + 1 = m → ∀ n, ¬ arrows.Adj m n := by
      intro m hm n
      simp [arrows]
      intro h' h''
      rw [← h''] at h'
      exact h' hm.symm
    -- The total number of bridges does not exceed the total number of arrows.
    have h4 : (G p).edgeFinset.card ≤ (Set.toFinset arrows.Adj.uncurry).card := by
      apply Finset.card_le_card_of_surjOn Sym2.mk
      intro e he
      cases' e with n m
      simp [G] at he
      obtain ⟨h_neq, he⟩ := he
      nth_rw 2 [or_comm] at he
      rw [or_self] at he
      rcases he with (he | he)
      · use ⟨n, m⟩
        simp
        exact ⟨h_neq, by linear_combination he⟩
      · use ⟨m, n⟩
        simp
        exact ⟨by solve_by_elim, by linear_combination he⟩
    -- Suppose $x^{2}-x+1 \equiv 0(\bmod p)$. We may assume that $1 \leqslant x \leqslant p$; then there is no arrow starting at $x$.
    have h5 : ∀ n, ¬ arrows.Adj x n := by
      apply h3
      linear_combination hx
    -- Since $(1-x)^{2}-(1-x)+1=x^{2}-x+1,(p+1-x)^{2}+1 \equiv(p+1-x)(\bmod p)$,
    have h6 : (1 - x)^2 - (1 - x) + 1 = x^2 - x + 1 := by ring
    have h7 : (p + 1 - x)^2 + 1 = p + 1 - x := by
      simp
      linear_combination hx
    -- and there is also no arrow starting at $p+1-x$.
    have h8 : ∀ n, ¬ arrows.Adj (p + 1 - x) n := by
      apply h3
      simp
      linear_combination hx
    --  If $x=p+1-x$, that is, $x=\frac{p+1}{2}$, then $4\left(x^{2}-x+1\right)=p^{2}+3$
    have h9 : (x = p + 1 - x) → 4 * (x^2 - x + 1) = p^2 + 3 := by
      intro h
      simp [ZMod.natCast_self] at *
      replace h : x * 2 = 1 := by linear_combination h
      ring_nf
      rw [show x^2 * 4 = (x * 2)^2 by ring, show x * 4 = (x * 2) * 2 by ring, h]
      norm_num
    -- and therefore $x^{2}-x+1$ is not divisible by $p$.
    have h10 : (x = p + 1 - x) → (x^2 - x + 1 ≠ 0) := by
      intro h
      apply h9 at h
      simp at h
      contrapose! h
      simp [h]
      change 0 ≠ ((3 : ℕ) : ZMod p)
      apply_fun ZMod.val
      simp only [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hp]
      norm_num
    -- Thus the islands $x$ and $p+1-x$ are different, and no arrows start at either of them.
    have h11 : x ≠ p + 1 - x := by
      intro h'
      exact h10 h' hx
    -- It follows that the total number of bridges in $p$-Landia does not exceed $p-2$.
    have h12 : (G p).edgeFinset.card ≤ p - 2 := by
      apply le_trans h4
      -- To show this we remove $x$ and $p + 1 - x$ from the set of vertices
      have : p - 2 = (((Finset.univ : Finset (ZMod p)).erase x).erase (p + 1 - x)).card := by
        rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem]
        · simp
          omega
        · simp
        · apply Finset.mem_erase_of_ne_of_mem h11.symm
          simp
      rw [this]
      -- and construct the surjection from the set of vertices onto the set of edges.
      apply Finset.card_le_card_of_surjOn (fun m ↦ ⟨m, m^2 + 1⟩)
      intro ⟨m, n⟩ h
      simp at h
      change m ≠ n ∧ m ^ 2 + 1 = n at h
      simp
      use m
      constructorm* _ ∧ _
      · intro h'
        subst h'
        apply h5 n
        simpa [arrows]
      · intro h'
        subst h'
        apply h8 n
        simpa [arrows]
      · rfl
      · exact h.right
    -- Let $1,2, \ldots, p$ be the vertices of a graph $G_{p}$, where an edge connects $m$ and $n$ if and only if there is a bridge between $m$ and $n$.
    -- The number of vertices of $G_{p}$ is $p$ and the number of edges is less than $p-1$.
    -- This means that the graph is not connected, which means that there are two islands not connected by a chain of bridges.
    contrapose! h12
    rw [← Nat.add_one_le_iff, show p - 2 + 1 = p - 1 by omega]
    -- Any connected graph must have at least $|V| - 1$ edges -- a very well-known fact that is missing in Mathlib.
    have edges_card_ge_of_connected {α : Type} [Fintype α] {G : SimpleGraph α} [Fintype G.edgeSet]
      (h : G.Connected) : Fintype.card α - 1 ≤ G.edgeFinset.card := sorry
    convert edges_card_ge_of_connected h12
    simp
  -- It remains to prove that there are infinitely many primes $p$ dividing $x^{2}-x+1$ for some integer $x$.
  suffices h' : {p | Nat.Prime p ∧ ∃ (x : ZMod p), x ^ 2 - x + 1 = 0}.Infinite by
    apply Set.Infinite.mono (s := {p | p.Prime ∧ (3 < p) ∧ (∃ (x : ZMod p), x^2 - x + 1 = 0)})
    · intro p ⟨h_prime, hp, hx⟩
      exact ⟨h_prime, h p h_prime hp hx⟩
    have h_inter : {p | p.Prime ∧ (3 < p) ∧ (∃ (x : ZMod p), x^2 - x + 1 = 0)} =
        {p | Nat.Prime p ∧ ∃ (x : ZMod p), x ^ 2 - x + 1 = 0} ∩ Set.Ioi 3 := by
      ext p
      simp
      tauto
    rw [h_inter]
    rw [← Set.diff_compl]
    apply Set.Infinite.diff h'
    simp
    apply Set.finite_Iic
  -- Let $p_{1}, p_{2}, \ldots, p_{k}$ be any finite set of such primes.
  intro h_fin
  let s := h_fin.toFinset
  -- Introduce $x = \left(p_{1} p_{2} \cdot \ldots \cdot p_{k}\right$.
  let x := s.prod id
  -- One can show that $x ≥ 7$ because 7 is such a prime ($7 | 3^2 - 3 + 1$).
  have hx0 : 7 ≤ x := by
    have h_pos : ∀ p ∈ s, 1 ≤ p := by
      simp [s]
      intro p h_prime x hx
      exact h_prime.one_le
    have h_7_mem : 7 ∈ s := by
      simp [s]
      norm_num
      use 3
      norm_num
      reduce_mod_char
    simp [x]
    rw [← Finset.insert_erase h_7_mem, Finset.prod_insert (by simp)]
    have : 1 ≤ ∏ x ∈ s.erase 7, x := by
      apply Finset.one_le_prod'
      intro p hp
      exact h_pos p (Finset.mem_of_mem_erase hp)
    omega
  -- The number $\left(p_{1} p_{2} \cdot \ldots \cdot p_{k}\right)^{2}-p_{1} p_{2} \cdot \ldots \cdot p_{k}+1$ is greater than 1
  have hx1 : 1 < x^2 - x + 1 := by
    have : 7 * x ≤ x^2 := by
      nlinarith
    omega
  -- and not divisible by any $p_{i}$;
  have hx2 : ∀ p ∈ s, ¬ p ∣ x^2 - x + 1 := by
    intro p hp
    have h_dvd : p ∣ x := Finset.dvd_prod_of_mem _ hp
    simp [← ZMod.natCast_zmod_eq_zero_iff_dvd] at h_dvd ⊢
    rw [Nat.cast_sub (by omega)]
    simp [h_dvd]
    apply_fun ZMod.val
    simp [s] at hp
    simp only [ZMod.val_zero, @ZMod.val_one p ⟨by linarith [hp.left.two_le]⟩]
    norm_num
  -- therefore it has another prime divisor with the required property.
  obtain ⟨p, h_prime, h_dvd⟩ := Nat.exists_prime_and_dvd hx1.ne.symm
  have hp : p ∉ s := by
    intro h
    apply hx2 _ h h_dvd
  -- And this leads to a contradiction.
  absurd hp
  simp [s]
  constructorm* _ ∧ _
  · exact h_prime
  · use x
    convert_to (x^2 - x + 1 : ℕ) = (0 : ZMod p)
    · simp
      rw [Nat.cast_sub (by omega)]
      simp
    rwa [ZMod.natCast_zmod_eq_zero_iff_dvd]
