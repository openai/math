import OAI.LinearAlgebra.MatrixExponent.RankCriterion
import OAI.LinearAlgebra.MatrixExponent.Descent
import OAI.LinearAlgebra.MatrixExponent.RankPower

/-!
# Invariance under field extension

Specialize the finitely many coefficients to a finite extension, take
tensor powers there, then pay the degree-squared overhead just once.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter

variable {F K : Type*} [Field F] [Field K] {a b c s : ℝ}

theorem RankLE.cut {i j k i' j' k' r : ℕ} (h : RankLE F i j k r)
    (hi : i' ≤ i) (hj : j' ≤ j) (hk : k' ≤ k) : RankLE F i' j' k' r := by
  obtain ⟨A, B, C, h⟩ := h
  let e {i j i' j' : ℕ} (hi : i' ≤ i) (hj : j' ≤ j) (x : Pos i' j') : Pos i j :=
    (Fin.castLE hi x.1, Fin.castLE hj x.2)
  refine ⟨fun l x => A l (e hi hk x), fun l y => B l (e hk hj y),
    fun l z => C l (e hi hj z), ?_⟩
  intro x y z
  simpa [e, Fin.ext_iff] using h (e hi hk x) (e hk hj y) (e hi hj z)

theorem exponent_le_of_rank {n i j k r : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hn : 2 ≤ n) (hi : side n a ≤ i) (hj : side n b ≤ j) (hk : side n c ≤ k)
    (hr : RankLE F i j k r) (hs : (r : ℝ) ≤ (n : ℝ) ^ s) : exponent F a b c ≤ s :=
  csInf_le ⟨_, fun _ h => areas_le_admissible h⟩ (admissible_of_rank hn ha hb hc hi hj hk hr hs)

private theorem rank_pos {n r : ℕ} (hn : 2 ≤ n)
    (hr : RankLE F (side n a) (side n b) (side n c) r) : 0 < (r : ℝ) := by
  have h : 0 < n := by omega
  exact_mod_cast (Nat.mul_pos (side_pos h a) (side_pos h b)).trans_le (hr.area (side_pos h c))

theorem exponent_lt_of_rank {n r : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hn : 2 ≤ n)
    (hr : RankLE F (side n a) (side n b) (side n c) r)
    (hs : (r : ℝ) < (n : ℝ) ^ s) : exponent F a b c < s := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast hn
  let t := Real.log (r : ℝ) / Real.log (n : ℝ)
  have ht : (n : ℝ) ^ t = r := by
    rw [Real.rpow_def_of_pos (by linarith), show Real.log (n : ℝ) * t = Real.log (r : ℝ) by
      dsimp [t]; exact mul_div_cancel₀ _ (Real.log_pos hn1).ne', Real.exp_log (rank_pos hn hr)]
  exact (exponent_le_of_rank ha hb hc hn le_rfl le_rfl le_rfl hr ht.ge).trans_lt
    ((Real.rpow_lt_rpow_left_iff hn1).mp (ht.trans_lt hs))

/-- A fixed cost multiplier is absorbed in a single sufficiently high power. -/
theorem absorb_overhead {n r D : ℕ} (hn : 2 ≤ n) (hr : 0 < (r : ℝ))
    (hs : (r : ℝ) < (n : ℝ) ^ s) :
    ∃ k : ℕ, 2 ≤ n ^ k ∧ ((r ^ k * D : ℕ) : ℝ) < ((n ^ k : ℕ) : ℝ) ^ s := by
  have ht := tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hr).mpr hs)
  obtain ⟨k, hk, hbig⟩ :=
    ((eventually_ge_atTop 1).and (ht.eventually_gt_atTop (D : ℝ))).exists
  refine ⟨k, hn.trans ?_, ?_⟩
  · simpa using pow_le_pow_right₀ (show 1 ≤ n by omega) hk
  · rw [div_pow, lt_div_iff₀ (pow_pos hr k)] at hbig
    rw [Nat.cast_mul, Nat.cast_pow r, Nat.cast_pow n, mul_comm]
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg n), mul_comm (k : ℝ),
      Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    exact hbig

private theorem descend_saving [Algebra F K] {n r : ℕ} (hn : 2 ≤ n)
    (hr : RankLE K (side n a) (side n b) (side n c) r) (hs : (r : ℝ) < (n : ℝ) ^ s) :
    ∃ N R : ℕ, 2 ≤ N ∧ RankLE F (side N a) (side N b) (side N c) R ∧
      (R : ℝ) < (N : ℝ) ^ s := by
  obtain ⟨L, _, _, _, hL⟩ := finiteExtensionRank (F := F) hr
  obtain ⟨k, hk, hbig⟩ := absorb_overhead (D := Module.finrank F L ^ 2) hn (rank_pos hn hr) hs
  have h := descendRank (F := F) (hL.pow k)
  exact ⟨_, _, hk, h.cut (side_pow le_rfl k) (side_pow le_rfl k) (side_pow le_rfl k), hbig⟩

theorem exponent_lt_iff_rank (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    exponent F a b c < s ↔
    ∃ n r : ℕ, 2 ≤ n ∧ RankLE F (side n a) (side n b) (side n c) r ∧
      (r : ℝ) < (n : ℝ) ^ s := by
  constructor
  · intro h
    obtain ⟨t, ht, hts⟩ := exists_lt_of_csInf_lt ⟨_, volume_admissible F ha hb hc⟩ h
    by_contra! hn
    apply hts.not_ge (le_admissible_of_cost ht ?_)
    intro n m hn' hm
    by_contra! hm'
    obtain ⟨N, R, hN, hR, hsave⟩ :=
      descend_saving (F := F) (s := s) hn' (bilinearize hm) (by exact_mod_cast hm')
    exact hsave.not_ge (hn N R hN hR)
  · rintro ⟨n, r, hn, hr, hs⟩
    exact exponent_lt_of_rank ha hb hc hn hr hs

theorem exponent_extension (F K : Type*) [Field F] [Field K] [Algebra F K]
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : exponent K a b c = exponent F a b c := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨n, r, hn, hr, hs⟩ := (exponent_lt_iff_rank ha hb hc).mp h
    exact lt_irrefl _ (exponent_lt_of_rank ha hb hc hn (hr.map (algebraMap F K)) hs)
  · by_contra! h
    obtain ⟨n, r, hn, hr, hs⟩ := (exponent_lt_iff_rank ha hb hc).mp h
    exact lt_irrefl _ ((exponent_lt_iff_rank ha hb hc).mpr (descend_saving (F := F) hn hr hs))

theorem cycle (F : Type*) [Field F] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    exponent F a b c = exponent F b c a := by
  apply le_antisymm <;> by_contra! h
  · obtain ⟨n, r, hn, hr, hs⟩ := (exponent_lt_iff_rank hb hc ha).mp h
    exact lt_irrefl _ (exponent_lt_of_rank ha hb hc hn hr.cycle.cycle hs)
  · obtain ⟨n, r, hn, hr, hs⟩ := (exponent_lt_iff_rank ha hb hc).mp h
    exact lt_irrefl _ (exponent_lt_of_rank hb hc ha hn hr.cycle hs)

theorem transpose (F : Type*) [Field F] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    exponent F a b c = exponent F b a c := by
  apply le_antisymm <;> by_contra! h
  · obtain ⟨n, r, hn, hr, hs⟩ := (exponent_lt_iff_rank hb ha hc).mp h
    exact lt_irrefl _ (exponent_lt_of_rank ha hb hc hn hr.transpose hs)
  · obtain ⟨n, r, hn, hr, hs⟩ := (exponent_lt_iff_rank ha hb hc).mp h
    exact lt_irrefl _ (exponent_lt_of_rank hb ha hc hn hr.transpose hs)

end OAI.LinearAlgebra.MatrixExponent.Rectangle

namespace OAI.LinearAlgebra.MatrixExponent

/-- The rank characterization for circuits with formal division. -/
theorem omega_lt_iff_rank {F : Type*} [Field F] {s : ℝ} : omega F < s ↔
    ∃ n r : ℕ, 2 ≤ n ∧ RankLE F n r ∧ (r : ℝ) < (n : ℝ) ^ s := by
  rw [← Rectangle.square, Rectangle.exponent_lt_iff_rank zero_le_one zero_le_one zero_le_one]
  simp only [Rectangle.side_one]
  rfl

theorem omega_extension (F K : Type*) [Field F] [Field K] [Algebra F K] :
    omega K = omega F := by
  simpa only [Rectangle.square] using
    Rectangle.exponent_extension F K zero_le_one zero_le_one zero_le_one

end OAI.LinearAlgebra.MatrixExponent
