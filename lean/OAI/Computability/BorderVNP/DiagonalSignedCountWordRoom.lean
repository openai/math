import OAI.Computability.BorderVNP.DiagonalFrozenSignedOperandRoom

/-! # The address of the last signed count in a compact cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Cover Crossing Epoch TeamScales Packing Inherited DeckGrid
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

private theorem four_mul_le_two_pow {k : ℕ} (hk : 4 ≤ k) : 4*k ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ]
    omega

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- The complete cell stack followed by one full hardware word per fixed
gadget fits in the native count-marker address, for all larger word choices
on the same calibrated processor and all sufficiently large lengths. -/
theorem JointSchedule.eventually_signed_count_room (b : JointSchedule s E deg Q A B j) (header gadgets : ℕ) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let L := S.publicProgramFactor^(epochs s.τ n)*initialMass (D:=D) n r d (width n s.α) header
      ∀ w ≥ 60*logWidth r n, 15*L + gadgets*w ≤ 2^w := by
  filter_upwards [b.eventually_programSeedStorage header,eventually_ge_atTop (gadgets+1)] with n storage hn
  intro r d L w hw
  have npos : 1≤n := by omega
  have small : width n (1/5:ℝ) ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast npos : 1≤(n:ℝ))
      (by norm_num : (1/5:ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have measured : 7*L ≤ width n (1/5:ℝ) := storage.2.1
  have cap : L≤n := by omega
  let h := logWidth r n
  have hr : 1 ≤ r := stretch_one ..
  have hpos : 1 ≤ h := (GeometryAdviceRate.indexWidths hr npos).1
  have dom : n ≤ 2^h := (Nat.size_le.mp (CellMacro.Generator.size_le_logWidth n r hr)).le
  change 60*h ≤ w at hw
  have units := four_mul_le_two_pow (k:=w-h) (by omega)
  calc
    15*L+gadgets*w ≤ 15*2^h+2^h*w :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (cap.trans dom)) (Nat.mul_le_mul_right _ ((by omega : gadgets ≤ n).trans dom))
    _ = 2^h*(15+w) := by ring
    _ ≤ 2^h*2^(w-h) := Nat.mul_le_mul_left _ ((by omega : 15+w ≤ 4*(w-h)).trans units)
    _ = 2^w := by rw [←pow_add,show h+(w-h)=w by omega]

end Diagonal

end BorderVNP
end Computability
end OAI
