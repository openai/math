import OAI.Hierarchy.GraphCutFamily
import OAI.Hierarchy.GraphWirePorts
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI
/-! # Orthogonal prescribed loads on graph cuts -/

namespace Hierarchy.IncidenceGraph

open scoped BigOperators Classical

noncomputable section

variable (G : IncidenceGraph)

/-- The left port carries the positive unit vector of its edge, and the right port
carries its negative. -/
def orthogonalSite (p : G.E × Bool) : EuclideanSpace ℝ (Fin (Fintype.card G.E)) :=
  let axis := EuclideanSpace.single (Fintype.equivFin G.E p.1) (1 : ℝ)
  if p.2 then -axis else axis

theorem orthogonalSite_unit (e : G.E) : ‖G.orthogonalSite (e, false)‖ = 1 := by
  simp [orthogonalSite]

theorem orthogonalSite_antipodal (e : G.E) :
    G.orthogonalSite (e, true) = -G.orthogonalSite (e, false) := rfl

private theorem cut_coord (U : Finset G.V) (e : G.E) :
    (∑ p ∈ Finset.univ.filter (fun p : G.E × Bool => G.portOwner p ∈ U),
      G.orthogonalSite p) (Fintype.equivFin G.E e) =
    (if G.left e ∈ U then (1 : ℝ) else 0) - (if G.right e ∈ U then 1 else 0) := by
  let coord := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (Fintype.card G.E) => ℝ)
    (Fintype.equivFin G.E e)
  change coord _ = _
  rw [map_sum, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single e]
  · by_cases hl : G.left e ∈ U <;> by_cases hr : G.right e ∈ U <;>
      simp [coord, hl, hr, orthogonalSite]
  · intro e' _ hne
    have different : Fintype.equivFin G.E e ≠ Fintype.equivFin G.E e' :=
      fun eqn => hne ((Fintype.equivFin G.E).injective eqn).symm
    by_cases hl : G.left e' ∈ U <;> by_cases hr : G.right e' ∈ U <;>
      simp [coord, hl, hr, different, orthogonalSite]
  · simp

/-- Each crossing edge contributes one squared coordinate and the two ends of
each internal edge cancel. -/
theorem norm_orthogonal_cut (U : Finset G.V) {w : ℝ} (hw : 0 ≤ w) :
    ‖∑ p ∈ Finset.univ.filter (fun p : G.E × Bool => G.portOwner p ∈ U),
      w • G.orthogonalSite p‖ = w * Real.sqrt ((G.boundaryEdges U).card : ℝ) := by
  let v := ∑ p ∈ Finset.univ.filter (fun p : G.E × Bool => G.portOwner p ∈ U),
    G.orthogonalSite p
  rw [← Finset.smul_sum, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
  apply congrArg (w * ·)
  change ‖v‖ = _
  rw [EuclideanSpace.norm_eq]
  apply congrArg Real.sqrt
  rw [← (Fintype.equivFin G.E).sum_comp (fun i => ‖v i‖ ^ 2)]
  calc
    ∑ e : G.E, ‖v (Fintype.equivFin G.E e)‖ ^ 2 =
        ∑ e : G.E, (if ¬(G.left e ∈ U ↔ G.right e ∈ U) then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [show v (Fintype.equivFin G.E e) = _ from G.cut_coord U e]
      by_cases hl : G.left e ∈ U <;> by_cases hr : G.right e ∈ U <;> simp [hl, hr]
    _ = _ := Finset.sum_boole (fun e : G.E => ¬(G.left e ∈ U ↔ G.right e ∈ U)) Finset.univ


end
end Hierarchy.IncidenceGraph

end OAI
