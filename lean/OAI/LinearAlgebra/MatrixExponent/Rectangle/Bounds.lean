import OAI.LinearAlgebra.MatrixExponent.CircuitCost
import OAI.LinearAlgebra.MatrixExponent.Bilinearize
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Universal arithmetic bounds and the coordinate planes -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter

variable {F : Type*} [Field F] {a b c s : ℝ}

@[simp] theorem side_one (n : ℕ) : side n 1 = n := by simp [side]

theorem square (F : Type*) [Field F] : exponent F 1 1 1 = MatrixExponent.omega F := by
  unfold exponent MatrixExponent.omega Admissible MatrixExponent.Admissible
  simp only [side_one]
  rfl

theorem side_pos {n : ℕ} (hn : 0 < n) (a : ℝ) : 0 < side n a :=
  Nat.ceil_pos.mpr (by positivity)

theorem side_le {n : ℕ} (hn : 0 < n) (ha : 0 ≤ a) :
    (side n a : ℝ) ≤ 2 * (n : ℝ) ^ a := by
  have h : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow (by exact_mod_cast hn) ha
  exact (Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith)

private theorem naive (F : Type*) [Field F] (i j k : ℕ) :
    ∃ m : ℕ, Computes F i j k m ∧ m ≤ i * j * (k * 2) := by
  have h (p : Pos i j) :
      CanMake (initial F i j k) (Fintype.card (Fin k) * 2) {output F p} :=
    CanMake.linear (Or.inl ⟨0, map_zero _⟩) (fun _ => Or.inr ⟨_, rfl⟩)
      (fun _ => Or.inr ⟨_, rfl⟩)
  obtain ⟨m, hm, T, hT, ho⟩ := CanMake.range h
  exact ⟨m, ⟨T, hT.embed, fun p => ho ⟨p, rfl⟩⟩, by simpa [Pos] using hm⟩

theorem volume_admissible (F : Type*) [Field F] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Admissible F a b c (a + b + c) := by
  intro ε hε
  refine ⟨16, by norm_num, ?_⟩
  intro n hn
  have hn₀ : 0 < (n : ℝ) := by positivity
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨m, hm, hcost⟩ := naive F (side n a) (side n b) (side n c)
  refine ⟨m, hm, ?_⟩
  calc
    (m : ℝ) ≤ (side n a : ℝ) * side n b * (side n c * 2) := by exact_mod_cast hcost
    _ ≤ (2 * (n : ℝ) ^ a) * (2 * (n : ℝ) ^ b) * (2 * (n : ℝ) ^ c * 2) := by
      gcongr <;> apply side_le <;> assumption
    _ = 16 * (n : ℝ) ^ (a + b + c) := by rw [Real.rpow_add hn₀, Real.rpow_add hn₀]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn₁ (by linarith)) (by norm_num)

/-- Any uniform polynomial lower bound on twice the circuit cost transfers
to every admissible exponent. -/
theorem le_admissible_of_cost (hs : Admissible F a b c s) {t : ℝ}
    (hl : ∀ n m : ℕ, 2 ≤ n → Computes F (side n a) (side n b) (side n c) m →
      (n : ℝ) ^ t ≤ 2 * m) : t ≤ s := by
  by_contra! hlt
  let ε := (t - s) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, _, hC⟩ := hs ε hε
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hp⟩ := ((eventually_ge_atTop 2).and (ht.eventually_gt_atTop (2 * C))).exists
  obtain ⟨m, hm, hcost⟩ := hC n (by omega)
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  apply (hl n m hn hm).not_gt
  calc
    2 * (m : ℝ) ≤ (2 * C) * (n : ℝ) ^ (s + ε) := by linarith
    _ < (n : ℝ) ^ ε * (n : ℝ) ^ (s + ε) := mul_lt_mul_of_pos_right hp (by positivity)
    _ = (n : ℝ) ^ t := by rw [← Real.rpow_add hn₀, show ε + (s + ε) = t by dsimp [ε]; ring]

private theorem area_cost {n m : ℕ} (hn : 0 < n)
    (h : side n a * side n b ≤ 2 * m) : (n : ℝ) ^ (a + b) ≤ 2 * m := by
  rw [Real.rpow_add (by positivity)]
  calc
    _ ≤ (side n a : ℝ) * side n b :=
      mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (by positivity) (by positivity)
    _ ≤ _ := by exact_mod_cast h

theorem areas_le_admissible (h : Admissible F a b c s) :
    max (a + b) (max (a + c) (b + c)) ≤ s := by
  refine max_le ?_ (max_le ?_ ?_) <;> apply le_admissible_of_cost h <;> intro n m hn hm
  · exact area_cost (by omega) ((bilinearize hm).area (side_pos (by omega) c))
  · rw [add_comm a c]
    exact area_cost (by omega) ((bilinearize hm).cycle.cycle.area (side_pos (by omega) b))
  · exact area_cost (by omega) ((bilinearize hm).cycle.area (side_pos (by omega) a))

theorem bounds (F : Type*) [Field F] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    max (a + b) (max (a + c) (b + c)) ≤ exponent F a b c ∧
      exponent F a b c ≤ a + b + c := by
  have h := volume_admissible F ha hb hc
  exact ⟨le_csInf ⟨_, h⟩ (fun _ ht => areas_le_admissible ht),
    csInf_le ⟨_, fun _ ht => areas_le_admissible ht⟩ h⟩

theorem coordinate_plane (F : Type*) [Field F] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a = 0 ∨ b = 0 ∨ c = 0) : exponent F a b c = a + b + c := by
  obtain ⟨hl, hu⟩ := bounds F ha hb hc
  refine le_antisymm hu ?_
  rw [max_le_iff, max_le_iff] at hl
  rcases h with h | h | h <;> linarith [hl.1, hl.2.1, hl.2.2]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
