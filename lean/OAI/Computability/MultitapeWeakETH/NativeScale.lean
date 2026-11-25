import OAI.Computability.MultitapeWeakETH.SparseExpansion
import OAI.Computability.VPVNP.CompressorPrefixLevelScale

/-! # Physical descriptor passes for the formula graph at the sparse volume scale -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open VPVNP Compression CompressorRecords CursorBounds DyadicBudget Filter
open scoped Classical
noncomputable section

variable {k R : Type} [Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)

/-- The descriptor theorem's RAM length is a polynomial in the sparse
volume. Its pass calendar has exactly the required number of blocks. -/
def scale (s : ℕ) := 2^(16*(stepSize B*s))

theorem scale_calendar (s : ℕ) : blockCount ((16*(stepSize B:ℝ))⁻¹) (scale B s) = s := by
  have hp : (0:ℝ) < stepSize B := by exact_mod_cast step_pos B
  have val : (16*(stepSize B:ℝ))⁻¹ * Real.logb 2 (scale B s) = s := by
    simp only [scale,Nat.cast_pow,Nat.cast_ofNat,Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2),
      Nat.cast_mul,mul_one]
    field_simp
  unfold blockCount
  rw [val,Nat.floor_natCast]

theorem scale_polynomial {N : ℕ} (hN : 1 < N) :
    scale B (index (4*stepSize B) N) ≤ (2^(4*stepSize B)*N)^4 := by
  have h := (grid_cover (b:=4*stepSize B) (by have := step_pos B; omega) hN).2
  apply le_trans _ (Nat.pow_le_pow_left h 4)
  rw [← pow_mul,scale]
  apply Nat.pow_le_pow_right (by decide)
  exact le_of_eq (by ring)

def source (s : ℕ) := CNFNetwork.inputState (S.degreeExponent 0) (3*(stepSize B*s)) (stepSize B*s)

private theorem source_shape (s : ℕ) :
    let u := stepSize B*s
    (source B s).positions = (8*u+4)*2^(3*u) ∧ (source B s).maxWireWidth ≤ 2^(u+2) := by
  intro u
  unfold source CNFNetwork.inputState
  rw [PackedSwitches.positions]
  refine ⟨?_,PackedSwitches.width_bound ..⟩
  congr 1
  change 2*(3*u+(u+2))-2+2 = 8*u+4
  omega

theorem source_positions {s : ℕ} (hs : 1 ≤ s) : (source B s).positions ≤ scale B s := by
  let u := stepSize B*s
  have pos : 1 ≤ u := Nat.mul_pos (step_pos B) hs
  rw [(source_shape B s).1]
  change (8*u+4)*2^(3*u) ≤ 2^(16*u)
  have h := Nat.mul_le_mul_right (2^(3*u)) (Nat.lt_two_pow_self (n:=8*u+4)).le
  exact h.trans (by rw [← pow_add]; apply Nat.pow_le_pow_right (by decide); omega)

theorem scale_ge (s : ℕ) : s ≤ scale B s := by
  have h : s ≤ stepSize B*s := Nat.le_mul_of_pos_left _ (step_pos B)
  exact (show s ≤ 16*(stepSize B*s) by omega).trans Nat.lt_two_pow_self.le

theorem cursor_positions {s : ℕ} (hs : 1 ≤ s) :
    (source B s).positions ≤ initialPositions 1 (scale B s) := by
  let n := scale B s
  have hn : 3 ≤ n := by
    have h : 1 ≤ stepSize B*s := Nat.mul_pos (step_pos B) hs
    exact (by decide : 3 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have dim : Nat.clog 2 n ≤ virtualBits 1 n := by
    simpa [addressBits,BurstRAM.addressWidth] using addressBits_le_virtualBits 1 n hn
  have vpos : 0 < virtualBits 1 n := lt_of_lt_of_le (Nat.clog_pos (by decide) (by omega)) dim
  exact (source_positions B hs).trans (((Nat.le_pow_clog (by decide : 1<2) n).trans
    (Nat.pow_le_pow_right (by decide) dim)).trans (Nat.le_mul_of_pos_right _ vpos))

theorem within (f : B.Entry → R) (hf : B.IsSolution f) {s : ℕ} (hs : 1 ≤ s) :
    PrefixLevelScale.Within (source B s).positions (scale B s)
      (B.execute f hf s (lanes_fit B s) (source B s)) := by
  let u := stepSize B*s
  have pos : 1 ≤ u := Nat.mul_pos (step_pos B) hs
  have width := (source_shape B s).2
  apply PrefixLevelScale.execute s (lanes_fit B s) _ le_rfl
  have w : (source B s).maxWireWidth+1 ≤ 2^(u+3) := by
      change (source B s).maxWireWidth ≤ 2^(u+2) at width
      rw [show u+3=u+2+1 by omega,pow_succ]
      have := Nat.two_pow_pos (u+2)
      omega
  apply (Nat.mul_le_mul (growth B s) w).trans
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by decide) (by change u+(u+3) ≤ 16*u; omega)

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
