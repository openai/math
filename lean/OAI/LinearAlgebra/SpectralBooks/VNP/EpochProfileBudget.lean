import OAI.LinearAlgebra.SpectralBooks.VNP.GadgetEquations

/-! # The per-block saving available from a fixed profile shape

The profile estimate for a single block at one term bounds the cost of
that term together with its selector. Thus the same shortening tables
give an epoch budget with the prescribed saving over every realizing field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
namespace VNP.ProfileShape
open Crossing

variable {D : ℕ} (P : ProfileShape D)

/-- The maximum wire budget after reserving the selector cost of one block. -/
def epochWireBudget : ℝ := (1-P.saving)*2*D*P.m - 2*D*P.bits

theorem cost_le_epochWireBudget (a : Fin P.terms) :
    ∑ i, wireCost (fun p q ↦ dist (axisPoint p) (axisPoint q)) (P.network.wires a i) ≤
      P.epochWireBudget := by
  classical
  let π : Fin P.terms → ℕ := fun u ↦ if u = a then 1 else 0
  have hπ : ∑ u, π u = 1 := by simp [π]
  have hdist (v : Fin D × Bool) : dist (axisPoint none) (axisPoint (some v)) = 1 := by
    obtain ⟨i,e⟩ := v
    cases e <;> simp [axisPoint]
  have hterm (u : Fin P.terms) :
      ∑ i, (↑(π u * (P.network.wires u i).width) : ℝ) *
        dist (axisPoint (P.network.wires u i).left) (axisPoint (P.network.wires u i).right) =
      if u = a then ∑ i, wireCost (fun p q ↦ dist (axisPoint p) (axisPoint q)) (P.network.wires a i) else 0 := by
    by_cases hu : u = a
    · subst u; simp [π, wireCost]
    · simp [π, hu]
  have h := P.profile_cost 1 π hπ
  simp only [profileWireCost, hterm] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hdist, one_mul, mul_one, Nat.cast_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at h
  unfold epochWireBudget
  linarith only [h]

/-- All masses, box shapes and local tables are inherited from the original shortening. -/
def epochNetwork {F : Type*} [Field F] {tables : P.Position → F} (h : P.Realizes tables) :
    CrossingNetworkSum F D P.m P.terms P.epochWireBudget where
  count := P.network.count
  wires := P.network.wires
  tables := (P.crossingNetworkSum h).tables
  realizes := (P.crossingNetworkSum h).realizes
  cost_le := P.cost_le_epochWireBudget

theorem epoch_saving : P.epochWireBudget + 2*D*P.bits ≤ (1-P.saving)*2*D*P.m := by
  rw [epochWireBudget, sub_add_cancel]

end VNP.ProfileShape

end

end SpectralBooks
end LinearAlgebra
end OAI
