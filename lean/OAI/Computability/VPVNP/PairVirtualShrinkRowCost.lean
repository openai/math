import OAI.Computability.VPVNP.LiveVirtualPairCursorBoundary
import OAI.Computability.VPVNP.PairShrinkHookRates
import OAI.Computability.VPVNP.PairShrinkSelectedExponentBound
import OAI.Computability.VPVNP.PairVertexRatedRoles
import OAI.Computability.VPVNP.PairVertexSelectedClock

/-!
# Resource bounds for shrinking rows of an actual virtual pair

The input-length threshold comes before the virtual pair, coefficients
and selected execution. Its wire-width envelope covers every input level.
A shrinking row can add at most a quadratic number of copies of any one
coefficient label. The complete histogram credit fits a machine word.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkRole

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords LocalHistory VertexImage
open TraversalRoles ShrinkNodeCost

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
    {labels : ℕ} (order : B.Entry ≃ Fin labels)
    {lanes : ℕ} (X : State (S.degreeExponent 0) lanes)

/-- Size and cost bounds for selected shrink rows of a virtual pair. They control the block
count, wire widths, available word credit, traversal rates and the number of resident field
copies. -/
structure RowBudget (n w T : ℕ) : Prop where
  positive : 1 ≤ n
  blocks : T ≤ n.log2+1
  width : B.growthConstant^T*(X.maxWireWidth+1) ≤ n
  credit : n*n^9000 < 2^w
  rate : RateRoom S (selectedHeaderLength B) (MapWitness.scanCoefficient B order)
    (prologueCoefficient B) n
  copies : ∀ j : Fin S.steps,
    2 * (MapResidentRows.capacity (S.degreeExponent j.castSucc) * fieldFactor B.shrink) ≤ n

variable {B order X} {n w T : ℕ} (budget : RowBudget B order X n w T)
variable {A : Type*} [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f)
    (hT : T * S.laneBits ≤ lanes) (z : (B.execute f ok T hT X).Choices)
local notation "passes" => executeLevels B f ok T hT X z
local notation "reader" v => originReader B f ok (SelectedLevel.origin v) (SelectedLevel.term v)

include budget

theorem RowBudget.later (i : Fin (passes).length) :
    (passes).length-(i.val+1) ≤ (S.steps+1)*(n.log2+1) :=
  selected_later_le_log B f ok T hT X z budget.blocks i.val

theorem RowBudget.old_width (i : Fin (passes).length) : (passes)[i].input.maxWireWidth ≤ n :=
  ((executeLevels_limits B f ok T hT X z _ (List.getElem_mem i.isLt)).2).trans budget.width

set_option exponentiation.threshold 10000 in
theorem RowBudget.label_count (i : Fin (passes).length)
    (shrinking : tagLevel B f ok (passes)[i] = .shrink) :
    ∀ u b a k l, ((reader ((passes).get i)).witness u a b).exponents k l ≤ n^9000 := by
  intro u b a k l
  have count := selected_exponent_le_square B f ok T hT X z i shrinking budget.positive
    budget.width budget.copies u b a k l
  exact count.trans
    (Nat.pow_le_pow_right budget.positive (by decide : 2 ≤ 9000))

end PairSimulation.ShrinkRole

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LiveProgram PairSimulation PairSimulation.VertexImage
open PairSimulation.ShrinkRole PairSimulation.ShrinkNodeCost Filter
open private blocks_le_log from OAI.Computability.VPVNP.CompressorDirectoryBudget

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant) {labels : ℕ}
    (order : B.Entry ≃ Fin labels)

attribute [local irreducible] BlockSchedule.Templates.execute CursorNetwork.cursorState

/-- The uniform shrinking allowance on the actual cursor input of each virtual pair. -/
theorem eventually_virtualShrinkRowCost (hb : max S.laneBits 5 ≤ D.addressFactor) (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn C) (A : Type*) [CommRing A]
      (f : B.Entry → A) (ok : B.IsSolution f)
      (_z : (B.execute f ok (blockCount (u.θ : ℝ) n) le_rfl V.scanState).Choices),
      RowBudget B order V.scanState n (D.geometry n).w (blockCount (u.θ : ℝ) n) := by
  filter_upwards [eventually_pairBranchBounds B u D.addressFactor hb,
    eventually_histogram_credit D.addressFactor D.address_pos,MapWitness.eventually_row_constants B,
    eventually_job_rate_room S (selectedHeaderLength B) (MapWitness.scanCoefficient B order)
      (prologueCoefficient B)]
    with n branch credit copies rate
  intro hn V A _ f ok
  rw [V.scanState_pairInput]
  intro z
  have field := (branch.2.2 (laneLabels _ _ V.lanes) V.dimension le_rfl A f ok z).2.2.2.2.2.1
  have size : (n : ℝ)^(3/10 : ℝ) ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr copies.1)
      (by norm_num : (3/10 : ℝ) ≤ 1)
  exact ⟨copies.1, blocks_le_log B u copies.1, Nat.cast_le (α := ℝ) |>.mp (field.trans size),
    credit, rate, copies.2⟩

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
