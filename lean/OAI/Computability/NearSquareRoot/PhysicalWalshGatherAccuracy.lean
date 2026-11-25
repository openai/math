import OAI.Computability.NearSquareRoot.PhysicalWalshGatherProgram
import OAI.Computability.NearSquareRoot.PrecisionEffectiveCutoff
import OAI.Computability.NearSquareRoot.SynchronizedGatherWalsh

/-! # Fixed-point accuracy of a Walsh pass on arbitrary selected address bits

The forward address permutation places the selected bits at the low end.
The inverse permutation restores the rounded records in original order;
both reindexings preserve Euclidean norm exactly.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open Matrix Filter IntegerMultiplication KernelPass FixedPoint

noncomputable section

/-- The gathered input at an address is the record at its inverse image. -/
def gatherInput {k : ℕ} (p : Equiv.Perm (Fin k)) (x : Fin (2^k) → Record k) : Fin (2^k) → Record k :=
  x ∘ (BoxFin.bitAddress p).symm

/-- The actual rounded low-field result restored to the original address order. -/
def gatherResult {a W k : ℕ} (hw : 0 < W) (plan : Plan (a+1) W W) (bits : Finset (Fin k))
    (p : Equiv.Perm (Fin k)) (x : Fin (2^k) → Record k) : Fin (2^k) → Record k :=
  Pieces.result hw plan k bits.card (lift (gatherInput p x)) ∘ BoxFin.bitAddress p

private theorem norm_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (v : EuclideanSpace ℂ κ) :
    ‖(WithLp.toLp 2 ((fun j => v j) ∘ e) : EuclideanSpace ℂ ι)‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq,EuclideanSpace.norm_eq]
  exact congrArg Real.sqrt (e.sum_comp (fun j => ‖v j‖^2))

/-- A grouped numerical certificate at this width also works after the two
physical address permutations, with exactly the same Euclidean tolerance. -/
theorem accurate_of_grouped {a W k : ℕ} (ha : 1 < a+1) (hw : 0 < W) (plan : Plan (a+1) W W)
    (grouped : ∀ (s : ℕ) (hs : s ≤ k) (z : ℕ → Record k),
      ‖recordArray (fun j : Fin (2^k) => z j.val)‖ ≤ (2:ℝ)^(13*k) →
      (Pieces.root k s z).Feasible hw plan ha ∧
      ‖recordArray (Pieces.result hw plan k s z) - WithLp.toLp 2
        (BoxFin.flatWalsh (FlatWalshWindow.bits k s 0 (by omega)) *ᵥ
          (fun i => FixedPoint.value k (z i.val)))‖ ≤ 1/(2:ℝ)^(50*k)) :
    ∀ (bits : Finset (Fin k)) (p : Equiv.Perm (Fin k)), (∀ i, (p i).val < bits.card ↔ i ∈ bits) →
    ∀ x : Fin (2^k) → Record k, ‖recordArray x‖ ≤ (2:ℝ)^(13*k) →
      (Pieces.root k bits.card (lift (gatherInput p x))).Feasible hw plan ha ∧
      ‖recordArray (gatherResult hw plan bits p x) - WithLp.toLp 2
        (BoxFin.flatWalsh bits *ᵥ (fun i => FixedPoint.value k (x i)))‖ ≤ 1/(2:ℝ)^(50*k) := by
  intro bits p hp x hx
  have hs : bits.card ≤ k := by simpa using bits.card_le_univ
  let e := BoxFin.bitAddress p
  let y := gatherInput p x
  have norm : ‖recordArray y‖ = ‖recordArray x‖ := norm_reindex e.symm (recordArray x)
  obtain ⟨good,err⟩ := grouped bits.card hs (lift y) (by simpa only [lift_fin] using norm.trans_le hx)
  refine ⟨good,?_⟩
  simp only [lift_fin] at err
  let M := BoxFin.flatWalsh (FlatWalshWindow.bits k bits.card 0 (by omega))
  let v := M *ᵥ (fun j => FixedPoint.value k (y j))
  have target : BoxFin.flatWalsh bits *ᵥ (fun j => FixedPoint.value k (x j)) = v ∘ e := by
    rw [BoxFin.flatWalsh_image bits p,BoxFin.gather_image bits p hp,BoxFin.lowBits_eq_window hs,
      submatrix_mulVec_equiv]
    rfl
  rw [target]
  exact (norm_reindex e (recordArray (Pieces.result hw plan k bits.card (lift y)) - WithLp.toLp 2 v)).le.trans err


/-- A primitive recursive cutoff in the plan's explicit growth majorant
supplies both reachability and accuracy after arbitrary bit regrouping. -/
theorem accurate_of_cutoff {a W k M : ℕ} (ha : 1 < a+1) (hw : 0 < W) (plan : Plan (a+1) W W)
    (hplan : Correct plan) (hc : PhysicalWalshNode.recursionFactor plan ≤ M)
    (hk : PhysicalWalshNode.precisionCutoff M ≤ k) :
    ∀ (bits : Finset (Fin k)) (p : Equiv.Perm (Fin k)), (∀ i, (p i).val < bits.card ↔ i ∈ bits) →
    ∀ x : Fin (2^k) → Record k, ‖recordArray x‖ ≤ (2:ℝ)^(13*k) →
      (Pieces.root k bits.card (lift (gatherInput p x))).Feasible hw plan ha ∧
      ‖recordArray (gatherResult hw plan bits p x) - WithLp.toLp 2
        (BoxFin.flatWalsh bits *ᵥ (fun i => FixedPoint.value k (x i)))‖ ≤ 1/(2:ℝ)^(50*k) :=
  accurate_of_grouped ha hw plan (Pieces.grouped_accurate_of_cutoff ha hw plan hplan hc hk)

/-- Every gathering permutation that puts exactly the selected positions into
the low field yields an admissible program and the finite-array error bound. -/
theorem eventually_accurate {a W : ℕ} (ha : 1 < a+1) (hw : 0 < W) (plan : Plan (a+1) W W)
    (hplan : Correct plan) : ∀ᶠ k : ℕ in atTop,
    ∀ (bits : Finset (Fin k)) (p : Equiv.Perm (Fin k)), (∀ i, (p i).val < bits.card ↔ i ∈ bits) →
    ∀ x : Fin (2^k) → Record k, ‖recordArray x‖ ≤ (2:ℝ)^(13*k) →
      (Pieces.root k bits.card (lift (gatherInput p x))).Feasible hw plan ha ∧
      ‖recordArray (gatherResult hw plan bits p x) - WithLp.toLp 2
        (BoxFin.flatWalsh bits *ᵥ (fun i => FixedPoint.value k (x i)))‖ ≤ 1/(2:ℝ)^(50*k) := by
  filter_upwards [Pieces.eventually_grouped_accurate ha hw plan hplan] with k grouped
  exact accurate_of_grouped ha hw plan grouped

end
end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
