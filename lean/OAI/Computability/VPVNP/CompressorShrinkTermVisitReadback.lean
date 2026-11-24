import OAI.Computability.VPVNP.CompressorShrinkTermPackets

/-!
# Operand readback of the two actual shrinking term visits

The planner expressions read the published shrinking level and allocator
origin. Their evaluated operands, initial cursors and exclusive stops are
the ones used by the chronological native packets.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkTermPackets

open BurstRAM BlockPlanner Compression PhaseRecipe ShrinkBlockInputs ShrinkInput
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps) (origin : Expr)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)

local notation "Z" => plan X start
local notation "q" => ShrinkRankSpace.Shape.collectBank (plan X start) w
local notation "rank" => ShrinkRAM.word w (ShrinkRankSpace.Shape.ranks (plan X start))
local notation "W" => widthBase X start
local notation "AB" => ShrinkWidthArena.abBase X q W
local notation "M" => ShrinkTermRecipe.M X
local notation "N" => ShrinkTermInputs.motifCount X

set_option maxHeartbeats 900000 in
theorem visit_readback (shape : DescriptorSpace.Shape) (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)
    (reads : ShrinkBundlePlan.Reads X shape i.val origin pub state mem start T)
    (room : termEnd X start 10 < 2^w) (j : Stage) :
    let v := visit B i origin j
    v.initial.eval pub state mem = 0 ∧ v.stop.eval pub state mem = (N : Word w) ∧
      (fun u => (v.params u).eval pub state mem) = bank B i origin X T start j := by
  let I := ShrinkBundlePlan.termInputs i.val (a i) origin
  have stopEq : ShrinkInput.stop X start = W+6*M+2*(Z).B := rfl
  change ShrinkInput.stop X start+2*M+M*10 < 2^w at room
  have fit : (Z).stop < 2^w := by change W < _; omega
  have hv := (Z).values T (placementBank X T start) Fintype.card_pos fit
  have hd : AB + 2*M = ShrinkInput.stop X start := by
    rw [stopEq]
    change W+2*((Z).B*(q 4).val)+2*((Z).B*(q 4).val)+2*(Z).B+2*M = _
    rw [hv.stride]
    change W+2*M+2*M+2*(Z).B+2*M = _
    omega
  have ready := ShrinkBundlePlan.term_input X reads fit
  have hc := (ShrinkTermRecipe.eval_count I X pub state mem ready).trans
    (congrArg (fun n : ℕ => (n : Word w)) (ShrinkTermRecipe.count_card X))
  cases j with
  | gather =>
    have data := ShrinkTermRecipe.gather_bank I X pub state mem ready (ShrinkWidthArena.prefixBase X q W)
      (thickBank X T start 4)
    change _ = ShrinkTermInputs.operands (cdBank X T start) (piecesBank X T start) ((AB+2*M : ℕ) : Word w) at data
    rw [hd] at data
    exact ⟨rfl,hc,data⟩
  | select =>
    have data := ShrinkTermRecipe.term_bank 10 I B.shrink SelectedScore.supplyOrder.entries X pub state mem ready
    change _ = TermWorker.motifData B.shrink finTwoEquiv SelectedScore.supplyOrder.entries w
      ![((AB+2*M : ℕ) : Word w),2,((AB+2*M+2*M : ℕ) : Word w),10] at data
    rw [hd] at data
    refine ⟨rfl,hc,data.trans ?_⟩
    change TermWorker.motifData B.shrink _ _ w _ = TermWorker.motifData B.shrink _ _ w _
    congr 1
    funext t
    fin_cases t <;> first | rfl | apply Fin.ext; exact (Nat.mod_mod _ _).symm

end CompressorRecords.ShrinkTermPackets

end VPVNP
end Computability
end OAI
