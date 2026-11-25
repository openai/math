import OAI.Computability.NearSquareRoot.InterchangeConfiguredBatch
import OAI.Computability.NearSquareRoot.InterchangeRepairSchedule
import OAI.Computability.NearSquareRoot.InterchangePredictRun

/-!
# Ground-field rows in a configured repair group

The lane, extension basis and Hamming label identify every independent
ground-field input. The cost of the four predictor calls and four
sweeps equals the configured call allowance.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.StageKernel

open OAI.LinearAlgebra.FiniteFourier SwapRepair StageRoute RepairSchedule
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom Support RectangleAtlas

variable {U : Type} {p k m b : ℕ} [Fact p.Prime] [NeZero b]
    {A : RectangleAtlas (nodeRectangles p k) (hammingReserve p k)}

/-- Physical row address of one independent input stream in a repair group. -/
abbrev GroupRow (p k m : ℕ) := PackedPencil.Index m × HammingLabels p k

theorem rowCount (p k m : ℕ) : Fintype.card (GroupRow p k m) =
    independentRows m * Fintype.card (HammingLabels p k) := by
  simp only [GroupRow, PackedPencil.Index, independentRows, Fintype.card_prod, Fintype.card_fin,
    componentWidth]

/-- The actual four predictor ledgers and the four auxiliary sweeps exactly
equal the price used in the configured node's contraction inequality. -/
theorem calls_eq_schedule (K : StageKernel p k m)
    (A : RectangleAtlas (nodeRectangles p k) (hammingReserve p k)) :
    let price := fun u : Move (nodeRectangles p k) (Fin m) K.source K.target => (A.routeWord u).price
    4 * (order m * (moveCharges (PackedPencil.Index m) price).count) +
      4 * Fintype.card (HammingLabels p k) * checks m * (Fintype.card (BasisIndex m) * m) =
      K.calls A := by
  intro price
  have hp : Fintype.card (PackedPencil.Index m) * StageScript.cost price K.program =
      (moveCharges (PackedPencil.Index m) price).count :=
    scalar_stage_cost (PackedPencil.Index m) K.matrix _ _ price (A.routeWord_price_idle _ _)
      (A.routeWord_price_align _ _) (A.routeWord_price_unalign _ _)
  rw [←hp]
  unfold calls correctedRows componentWidth
  change 4 * (order m * (Fintype.card (PackedPencil.Index m) * StageScript.cost price K.program)) + _ =
    4 * order m * (Fintype.card (PackedPencil.Index m) * StageScript.cost price K.program) + _
  ring

/-- Assemble native independent rows into the extension description for the
pointwise Hermite tables. Every component of every label is occupied. -/
def packGroup {X : U → Type} (x : (i : U) → GroupRow p k m → X i → ZMod p) :
    (i : U) → Data (ZMod p) (HammingLabels p k) (X i) (width m) m :=
  fun i w t a => (components (ZMod p) m).symm (fun d => x i ((t,d),w) a)

@[simp] theorem streams_packGroup {X : U → Type} (x : (i : U) → GroupRow p k m → X i → ZMod p) :
    streams (packGroup x) = x := by
  funext i u a
  rcases u with ⟨⟨t,d⟩,w⟩
  exact congrFun ((components (ZMod p) m).apply_symm_apply _) d

end Interchange.StageKernel

end

end NearSquareRoot
end Computability
end OAI
