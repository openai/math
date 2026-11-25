import OAI.Computability.MultitapeWeakETH.CompressionCounts
import OAI.Computability.VPVNP.CompressionBudget

/-! # The savings on a dyadic grid of input volumes

For grid index s, put u = Ks, allocate 3u lane bits and u site-offset bits,
and perform s blocks. Increasing s by one changes the capacity by only the
fixed factor 2^(4K). Along the grid the local sum, selector and shared-wire
bounds all save at least s bits in the volume exponent, up to polynomials.
-/

namespace OAI.Computability.MultitapeWeakETH.DyadicBudget

open VPVNP Compression NetworkKernel PairSimulation.LocalHistory
open scoped Classical
noncomputable section

theorem initial_energy {a g : ℕ} (X : State a g) : Real.sqrt X.energy ≤
    (X.positions : ℝ) * (2^a : ℕ) * X.maxWireWidth := by
  have hc : Fintype.card ((X.Base × Fin (2^a)) × BitWord g) = X.positions * 2^a := by
    simp only [State.positions,Fintype.card_prod,Fintype.card_fin]
    ac_rfl
  exact regularWire_sqrtEnergy_le X.width hc X.width_le_maxWireWidth

variable {k R : Type} [Field k] [Field R] {S : BlockSchedule k} (B : S.Templates)

def stepSize := max 1 (max S.laneBits (Nat.clog 2 B.growthConstant))

theorem step_pos : 1 ≤ stepSize B := le_max_left ..

theorem lanes_fit (s : ℕ) : s*S.laneBits ≤ 3*(stepSize B*s) := by
  have h : S.laneBits ≤ stepSize B := (le_max_left ..).trans (le_max_right ..)
  have := Nat.mul_le_mul_right s h
  rw [Nat.mul_comm s]; omega

theorem growth (s : ℕ) : B.growthConstant^s ≤ 2^(stepSize B*s) := by
  rw [pow_mul]
  apply Nat.pow_le_pow_left
  apply (Nat.clog_le_iff_le_pow (by decide)).mp
  exact (le_max_right ..).trans (le_max_right ..)

variable (f : B.Entry → R) (hf : B.IsSolution f) (s : ℕ)
    (X : State (S.degreeExponent 0) (3*(stepSize B*s)))

/-- Logarithmic cost of one terminal site's monomial choice. -/
theorem private_bits (width : X.maxWireWidth ≤ 2^(stepSize B*s+2)) :
    B.growthConstant^s * (B.growthConstant^s * (X.maxWireWidth+1)) ≤
      2^(3*(stepSize B*s)+3) := by
  let u := stepSize B*s
  have grow := growth B s
  have one : X.maxWireWidth+1 ≤ 2^(u+3) := by
    have : 0 < 2^(u+2) := Nat.two_pow_pos _
    change X.maxWireWidth ≤ 2^(u+2) at width
    rw [show u+3 = (u+2)+1 by omega,pow_succ]; omega
  calc
    _ ≤ 2^u*(2^u*2^(u+3)) := Nat.mul_le_mul grow (Nat.mul_le_mul grow one)
    _ = _ := by rw [← pow_add,← pow_add]; congr 1; dsimp [u]; omega

private theorem s_le_u : s ≤ stepSize B*s := Nat.le_mul_of_pos_left _ (step_pos B)

/-- The selector count uses only polynomially many bits per processor. -/
theorem selector_bits (width : X.maxWireWidth ≤ 2^(stepSize B*s+2)) :
    let u := stepSize B*s
    let c := scanConstant B
    ((S.steps+1)*s) * (X.positions*c*(c+Nat.clog 2 (B.growthConstant^s*(X.maxWireWidth+1)+1))) ≤
      ((S.steps+1)*s) * (X.positions*c*(c+(2*u+4))) := by
  dsimp only
  gcongr
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  let u := stepSize B*s
  have one : X.maxWireWidth+1 ≤ 2^(u+3) := by
    have := Nat.two_pow_pos (u+2)
    change X.maxWireWidth ≤ 2^(u+2) at width
    rw [show u+3 = (u+2)+1 by omega,pow_succ]; omega
  have bound := Nat.mul_le_mul (growth B s) one
  change B.growthConstant^s * (X.maxWireWidth+1) ≤ 2^u*2^(u+3) at bound
  rw [← pow_add] at bound
  change _ ≤ 2^(2*u+4)
  rw [show 2*u+4 = (u+(u+3))+1 by omega,pow_succ]
  have := Nat.two_pow_pos (u+(u+3))
  omega

/-- All assignments on one branch use this many shared bits. This is where
the s blocks save the factor 2^s over a linear-volume enumeration. -/
theorem shared_bits (width : X.maxWireWidth ≤ 2^(stepSize B*s+2))
    (positions : X.positions = (8*(stepSize B*s)+4)*2^(3*(stepSize B*s)))
    (z : (B.execute f hf s (lanes_fit B s) X).Choices) :
    let u := stepSize B*s
    (((B.execute f hf s (lanes_fit B s) X).finalState z).totalWidth : ℝ) ≤
      (8*(u:ℝ)+4)*(4*(2:ℝ)^(S.degreeExponent 0)+B.widthAllowance)*(2:ℝ)^(4*u-s) := by
  let u := stepSize B*s
  let d := (2:ℝ)^(S.degreeExponent 0)
  obtain ⟨_,h₁,h₂,_⟩ := B.branch_bounds f hf s (lanes_fit B s) X z
  apply (h₁.trans h₂).trans
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^s)).mpr
  have hw : (X.maxWireWidth : ℝ) ≤ (2:ℝ)^(u+2) := by exact_mod_cast width
  have he := initial_energy X
  push_cast at he
  have hp : (X.positions : ℝ) = (8*(u:ℝ)+4)*2^(3*u) := by exact_mod_cast positions
  have hd : 0 ≤ d := by positivity
  have hA : 0 ≤ B.widthAllowance := Real.sqrt_nonneg _
  have hu : s ≤ u := s_le_u B s
  have powers : (2:ℝ)^(4*u-s)*2^s = (2:ℝ)^(4*u) := by rw [← pow_add]; congr 1; omega
  change _ ≤ ((8*(u:ℝ)+4)*(4*d+B.widthAllowance)*2^(4*u-s))*2^s
  rw [mul_assoc _ ((2:ℝ)^(4*u-s)),powers]
  calc
    _ ≤ (X.positions : ℝ)*d*2^(u+2) + B.widthAllowance*X.positions :=
      add_le_add (he.trans (mul_le_mul_of_nonneg_left hw (by positivity))) le_rfl
    _ ≤ (X.positions : ℝ)*d*2^(u+2) + B.widthAllowance*X.positions*2^u := by
      exact add_le_add le_rfl (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
    _ = _ := by
      rw [hp,show 4*u = 3*u+u by omega,pow_add (2:ℝ) (3*u) u,pow_add (2:ℝ) u 2]; ring


end
end OAI.Computability.MultitapeWeakETH.DyadicBudget
