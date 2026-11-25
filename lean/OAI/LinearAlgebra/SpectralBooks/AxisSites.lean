import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Sym.Card

/-! # The center, signed unit vectors, and unordered pairs of sites in the crossing -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Crossing

noncomputable section

/-- The center and the signed coordinate axes. -/
abbrev AxisSite (D : ℕ) := Option (Fin D × Bool)

/-- The placements of the marked sites in the unit ball. -/
def axisPoint {D : ℕ} : AxisSite D → EuclideanSpace ℝ (Fin D)
  | none => 0
  | some (i, b) => EuclideanSpace.single i (if b then 1 else -1)

theorem axisPoint_in_ball {D : ℕ} (i : AxisSite D) :
    axisPoint i ∈ Metric.closedBall 0 1 := by
  rcases i with _ | ⟨i, b⟩
  · simp [axisPoint]
  · cases b <;> simp [axisPoint, Metric.mem_closedBall]

theorem axisPoint_injective (D : ℕ) : Function.Injective (axisPoint (D := D)) := by
  intro p q h
  rcases p with _ | ⟨i, a⟩ <;> rcases q with _ | ⟨j, b⟩
  · rfl
  · have hnorm := congrArg norm h
    cases b <;> norm_num [axisPoint] at hnorm
  · have hnorm := congrArg norm h
    cases a <;> norm_num [axisPoint] at hnorm
  · have hi := congrArg (fun v : EuclideanSpace ℝ (Fin D) => v i) h
    by_cases hij : i = j
    · subst j
      cases a <;> cases b <;> first | rfl | norm_num [axisPoint, EuclideanSpace.single, PiLp.single_apply] at hi
    · cases a <;> cases b <;> norm_num [axisPoint, EuclideanSpace.single, PiLp.single_apply, hij] at hi

/-- The unordered pairs of distinct sites in the proof of the alternative. -/
abbrev AxisPair (D : ℕ) := {e : Sym2 (AxisSite D) // ¬e.IsDiag}

theorem card_axisPair (D : ℕ) : Fintype.card (AxisPair D) = (2 * D + 1).choose 2 := by
  rw [Sym2.card_subtype_not_diag]
  simp [AxisSite, mul_comm]

theorem endpoints_ne {D : ℕ} (e : AxisPair D) : e.val.out.1 ≠ e.val.out.2 := by
  intro h
  apply e.prop
  have he : Sym2.mk e.val.out.1 e.val.out.2 = e.val := by
    rw [Sym2.mk, Prod.mk.eta, e.val.out_eq]
  rw [← he, Sym2.mk_isDiag_iff]
  exact h

def axisLength {D : ℕ} (e : AxisPair D) : ℝ :=
  dist (axisPoint e.val.out.1) (axisPoint e.val.out.2)

theorem axisLength_pos {D : ℕ} (e : AxisPair D) : 0 < axisLength e :=
  dist_pos.mpr fun h => endpoints_ne e (axisPoint_injective D h)

end
end Crossing

end SpectralBooks
end LinearAlgebra
end OAI
