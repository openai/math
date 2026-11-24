import OAI.Computability.VPVNP.EvaluatorScheduleEffects
import OAI.Computability.VPVNP.EvaluatorOutput

/-!
# The residue of the scheduler's actual index choices

The continuation of the nested digit loops stores the current basis ordinal
and the accumulated scalar. At termination its ordinary integer multiplicity
is the constant-coordinate residue at the unit ordinal and zero elsewhere.
Expanding the continuation over the chronological actions gives exactly the
matrix-index paths of the finite algebra.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator

open EvaluatorScheduleEffects EvaluatorDigitSchedule

variable {I K A : Type*} [Fintype I] [DecidableEq I] [Field K] [Fintype K]
    [CommRing A] [Algebra K A] {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K]
    [Algebra (ZMod p) A] [IsScalarTower (ZMod p) K A] {t Z : ℕ}
    (b : Module.Basis I K A) (unit : I) (coord : K →ₗ[ZMod p] ZMod p)

/-- The endpoint test used by the terminal field reader. -/
def finishWeight (s : I × K) : ℕ := if s.1 = unit then (coord s.2).val else 0

/-- A transition multiplies the old accumulator by row `j`, column `s.1`
of the current linear map. The index `j` is the next binary guess. -/
noncomputable def indexTransition (M : A →ₗ[K] A) (s : I × K) (j : I) : I × K :=
  (j, s.2 * (LinearMap.toMatrixAlgEquiv b M) j s.1)

/-- The ordinal of a label is read from the scheduler's current unary counter.
All live ordinal values are in range. -/
noncomputable def nextIndex (X : Fin t → A) (op : Option ℕ) : I × K → I → I × K :=
  indexTransition b (match op with
    | none => (FiniteField.frobeniusAlgHom K A).toLinearMap
    | some i => if hi : i < t then LinearMap.mulLeft K (X ⟨i,hi⟩) else 0)

omit [Fintype K] in
private theorem foldr_count (ms : List (Matrix I I K)) (s : I × K) :
    ms.foldr (fun m f (q : I × K) ↦ ∑ j, f (j, q.2 * m q.1 j)) (finishWeight unit coord) s =
      ∑ path : IndexPath.{_,0} I ms.length, (coord (s.2 * pathWeight ms s.1 unit path)).val := by
  induction ms generalizing s with
  | nil =>
    change finishWeight unit coord s =
      ∑ _ : PUnit, (coord (s.2 * (if s.1 = unit then 1 else 0))).val
    by_cases he : s.1 = unit <;> simp [finishWeight, he]
  | cons m ms ih =>
    simp only [List.foldr_cons, ih]
    change _ = ∑ path : I × IndexPath.{_,0} I ms.length,
      (coord (s.2 * (m s.1 path.1 * pathWeight ms path.1 unit path.2))).val
    rw [Fintype.sum_prod_type]
    simp only [mul_assoc]

omit [Algebra (ZMod p) A] [IsScalarTower (ZMod p) K A] in
/-- The ordinary count of the nested digit loops is the number of accepting
index paths with their final residue multiplicities. -/
theorem schedulerEffect_eq_card (X : Fin t → A) (e : Fin t → BurstRAM.Word Z) :
    schedulerEffect (nextIndex b X) e (Fintype.card K) (finishWeight unit coord) (unit,1) =
      Fintype.card (AcceptingBranches.{_,_,0} coord
        (transitionMatrices b (digitProgram K X Z (fun i ↦ (e i).val))) unit unit) := by
  rw [schedulerEffect_eq_digitProgram K X (nextIndex b X)
    (fun m f q ↦ ∑ j, f (indexTransition b m q j)) (by
      intro op
      funext f q
      cases op <;> simp [stepEffect, actionCode, nextIndex, actionMap])]
  let ms := digitProgram K X Z (fun i ↦ (e i).val)
  have h := foldr_count unit coord (transitionMatrices b ms) (unit, 1)
  unfold AcceptingBranches
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simpa only [transitionMatrices, List.foldr_map, indexTransition, Matrix.transpose_apply,
    one_mul, ms] using h

/-- Equation (8.2) for the physical scheduler's ordinary path-count effect. -/
theorem schedulerEffect_mod (hunit : b unit = 1) (X : Fin t → A) (e : Fin t → BurstRAM.Word Z) :
    (schedulerEffect (nextIndex b X) e (Fintype.card K) (finishWeight unit coord) (unit,1) : ZMod p) =
      primeFunctional b unit coord (∏ i, X i ^ (e i).val) := by
  rw [schedulerEffect_eq_card]
  exact finiteAlgebra_pathCount b unit hunit coord X Z _ (fun i ↦ (e i).isLt)

end Evaluator

end VPVNP
end Computability
end OAI
