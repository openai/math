import OAI.Computability.NearSquareRoot.KernelPassStageFrequency
import OAI.Computability.NearSquareRoot.KernelPassGeometry
import OAI.Computability.NearSquareRoot.KernelBinaryQueryRational
import OAI.Computability.NearSquareRoot.KernelPassSaving

/-! # Dyadic coefficients of the physical rectangle pencil

A bank has one independent rational row for each basis coordinate of each clock lane.
The same finite coefficient tables work at every address width and at every label.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Plan

open CyclotomicCode PencilDyadicMix PencilSearch PencilCoordinates PencilDescent
open RepairCoordinates Matrix

open Rect (StageRow)

/-- Literal finite coefficient in the constant term or one queried term of the stage. -/
def stageCoefficient {m : ℕ} (hm : 2 ≤ m) (q : Option (Fin m)) (u v : StageRow m) :
    Coefficient :=
  encode (flatten (indexedCoefficient (rowIndex m (clockDigits m) (clockPeriod m))
    (batchPencil m hm) q) u v)

theorem stageCoefficient_value {m : ℕ} (hm : 2 ≤ m) (q : Option (Fin m)) (u v : StageRow m) :
    value (stageCoefficient hm q u v) =
      flattenRat (indexedCoefficient (rowIndex m (clockDigits m) (clockPeriod m))
        (batchPencil m hm) q) u v := by
  exact value_encode _

/-- Evaluating the signed row coefficients at a frequency gives exactly the Hermite stage. -/
theorem stageMatrix_entry {m : ℕ} (hm : 2 ≤ m) (k : Signature m) (u v : StageRow m) :
    stageMatrix hm k u v = value (stageCoefficient hm none u v) +
      ∑ j, (-1 : ℚ) ^ (k j).val * value (stageCoefficient hm (some j) u v) := by
  unfold stageMatrix rationalStage
  change _ + (∑ j : Fin m, (-1 : ℚ) ^ (k j).val • flattenRat (indexedCoefficient _ _ (some j))) u v = _
  rw [Matrix.sum_apply]
  simp only [stageCoefficient_value, Matrix.smul_apply, smul_eq_mul]
  congr 1

end KernelPass.Plan

namespace KernelPass.Rect.Binary

open Matrix Plan KernelPassSaving
open scoped CyclotomicCode

variable {L b m N h : ℕ}

/-- Enumerate the complete physical geometric label bank. -/
noncomputable def labelIndex (L b : ℕ) : Label L b ≃ Fin (labels L b) :=
  (Fintype.equivFin _).trans (finCongr card_label)

/-- The one rectangle pencil, including its actual dyadic clock coefficients
and the fixed order of all label and component rows. -/
noncomputable def generatedStage (S : System L b) (hm : 2 ≤ m+1) (e : Label L b ≃ Fin N) :
    Plan (BinaryQuery.Arity (m+1) (S.D-1)) (N * basisWidth (m+1)) (N * basisWidth (m+1)) :=
  renumber (stageIndex e (m+1)) <| geometricPencil S m
    (stageCoefficient hm none) (fun j => stageCoefficient hm (some j))

theorem generatedStage_calls (S : System L b) (hm : 2 ≤ m+1) (e : Label L b ≃ Fin N) :
    (generatedStage S hm e).calls ≤ stageBound L b (m+1) S.D := by
  refine (calls_renumber (stageIndex e (m+1)) (geometricPencil S m
    (stageCoefficient hm none) (fun j => stageCoefficient hm (some j)))).le.trans ?_
  simpa only [StageRow, Fintype.card_prod, Fintype.card_fin, PencilDescent.Coord,
    stageBound, expandedWidth, labels] using
    calls_geometricPencil S m (stageCoefficient hm none) (fun j => stageCoefficient hm (some j))

/-- Every physical address width and every label has the rational stage used
by the correction program. The spectral sign comes from the routed query. -/
theorem generatedStage_frequency (S : System L b) (hm : 2 ≤ m+1) (e : Label L b ≃ Fin N)
    (w : Label L b) (x : Bank (BinaryQuery.Arity (m+1) (S.D-1)) h (N * basisWidth (m+1)))
    (y : Addr (BinaryQuery.Arity (m+1) (S.D-1)) h) :
    labelSlice e w y ((generatedStage S hm e).applyAt h x) =
      stageMatrix hm (∑ t, BinaryQuery.test (m+1) (S.D-1) (y t)) *ᵥ labelSlice e w y x := by
  apply labelSlice_stage hm e _
    (fun k l => value (stageCoefficient hm none k l))
    (fun j k l => value (stageCoefficient hm (some j) k l))
    (fun _ y => ∑ t, BinaryQuery.test (m+1) (S.D-1) (y t))
    (fun j _ => rationalLift h (BinaryQuery.query (u := S.D-1) j))
  · exact block_geometricPencil S m _ _ h
  · exact fun j _ v z => BinaryQuery.rational_frequency j v z
  · exact fun t k l => (stageMatrix_entry hm t k l).symm

end KernelPass.Rect.Binary

end NearSquareRoot
end Computability
end OAI
