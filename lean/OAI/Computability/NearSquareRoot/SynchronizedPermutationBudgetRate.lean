import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetBox
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetVolume
import OAI.Computability.NearSquareRoot.PhysicalWalshXorReserve

/-! # The guard, row clock, and physical volume of a synchronized permutation batch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPermutationBudget

open IntegerMultiplication Packed Controlled

/-- An integral clock for twice the interchange rate on a window of at most `k` bits. -/
noncomputable def rowFactor (k : ℕ) (ρ : ℝ) : ℕ := ⌈2*((k:ℝ)+1)^ρ⌉₊

theorem row_rate {k h : ℕ} {ρ : ℝ} (hh : h ≤ k) (hρ : 0 ≤ ρ) :
    2*((h:ℝ)+1)^ρ ≤ rowFactor k ρ := by
  have le : (h:ℝ)+1 ≤ (k:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hh
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) le hρ) (by norm_num)).trans
    (Nat.le_ceil _)

theorem row_factor_time (k : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (rowFactor k ρ : ℝ) + 1 ≤ 4*((k:ℝ)+1)^ρ := by
  have h := (Nat.ceil_lt_add_one (a := 2*((k:ℝ)+1)^ρ) (by positivity)).le
  have pos : 1 ≤ ((k:ℝ)+1)^ρ := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) k]) hρ
  unfold rowFactor
  linarith

theorem row_factor_high {k : ℕ} (hk : 1 ≤ k) {ρ : ℝ} (hρ : ρ ≤ 1) :
    rowFactor k ρ ≤ 2^(payloadBits 2 k) := by
  apply Controlled.rowFactor_le (f := 2) (A := payloadBits 2 k) _ le_rfl
  apply Nat.ceil_le.mpr
  have one : 1 ≤ (k:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have major := Real.rpow_le_rpow_of_exponent_le one hρ
  simp only [Real.rpow_one] at major
  have two : (2:ℝ) ≤ k+1 := by exact_mod_cast Nat.succ_le_succ hk
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right two (show 0 ≤ (k:ℝ)+1 by positivity)]

/-- Actual arithmetic inputs to the sparse repair of a guarded XOR. -/
theorem sparse_of_fits {k b : ℕ} (fit : (b+1)*guardWidth k ≤ k) :
    (3*cap b (guardWidth k-1) 0+1)*(32*b) ≤ 2^(Packed.width (guardWidth k-1) 0) := by
  have pos : 0 < guardWidth k := by unfold guardWidth; omega
  have eq : Packed.width (guardWidth k-1) 0 = guardWidth k := by unfold Packed.width; omega
  have count : b ≤ k :=
    (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ pos).trans fit)
  change (3*((b+1)*Packed.width (guardWidth k-1) 0)+1)*(32*b) ≤ _
  rw [eq]
  exact guardWidth_pays fit count

namespace BoxPasses
variable {k D : ℕ} (budget : BoxPasses k D 2)
include budget

/-- The two reserve widths and the middle gap give the exact uncompressed array
volume. The integral rate fits the high prefix for every exponent in the paper's
range. Both auxiliary inequalities use the *actual* number of selected blocks. -/
theorem row_bounds (hk : 1 ≤ k) (a : ℕ) (selected : Finset (Fin ((CoprimeBox.box k).length / 4)))
    (sub : selected ⊆ members k a) {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) (record : ℕ) :
    let p := ∑ i ∈ selected, (BoxFin.physicalWidth (box := CoprimeBox.box k) i - 1)
    let b := selected.card
    let chunk := (b+1)*guardWidth k
    let low := payloadBits D k
    let high := payloadBits 2 k
    let gap := k - (high+p+chunk+chunk+low)
    let middle := p+chunk+gap+chunk
    PhysicalWalsh.XorReserve.volume high middle low record = 2^k*record ∧
      2*((chunk:ℝ)+1)^ρ ≤ rowFactor k ρ ∧ rowFactor k ρ ≤ 2^high ∧
      (3*cap b (guardWidth k-1) 0+1)*(32*b) ≤ 2^(Packed.width (guardWidth k-1) 0) := by
  let p := ∑ i ∈ selected, (BoxFin.physicalWidth (box := CoprimeBox.box k) i - 1)
  let chunk := (selected.card+1)*guardWidth k
  let low := payloadBits D k
  let high := payloadBits 2 k
  let middle := p+chunk+(k-(high+p+chunk+chunk+low))+chunk
  have split : high+middle+low = k := budget.layout a selected sub
  have le : chunk ≤ k := by dsimp [middle] at split; omega
  exact ⟨by change 2^(high+middle+low)*record = _; rw [split],
    row_rate le h₀, row_factor_high hk h₁, sparse_of_fits le⟩

end BoxPasses
end SynchronizedPermutationBudget

end NearSquareRoot
end Computability
end OAI
