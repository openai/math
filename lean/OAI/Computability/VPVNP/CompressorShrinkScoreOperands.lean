import OAI.Computability.VPVNP.CompressorShrinkScoreVisits
import OAI.Computability.VPVNP.CompressorShrinkABSliceOperands
import OAI.Computability.VPVNP.CompressorShrinkHeaderReads
import OAI.Computability.VPVNP.CompressorGreedyPlannerFootprint
import OAI.Computability.VPVNP.CompressorShrinkInputTerms

/-! # Score operands in the actual shrinking block header -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ScorePackets

open BurstRAM Compression BlockPlanner ShrinkBlockInputs DescriptorSpace PhaseRecipe
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
local notation "F" => BlockProgram.geometry B
local notation "O" => BlockProgram.arena B i.val 0
local notation "I" => selectedInputs B (BlockProgram.geometry B) i (BlockProgram.arena B i.val 0)
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "N" => SelectedArena.motifs X

theorem start_le_term (room : ShrinkInput.termEnd X start 10 < 2^w) : start ≤ (term).val := by
  let M := ShrinkTermRecipe.M X
  have earlier : start ≤ ShrinkInput.widthBase X start := by
    have greedy := GreedyArena.greedyStop_eq start (Fintype.card X.Base) (a i)
    change start ≤ (((((ShrinkInput.placementBase X start+_)+_)+_)+_)+_)+_
    change ShrinkInput.placementBase X start = start+_+_ at greedy
    omega
  change ShrinkInput.widthBase X start+_+_+2*M+M*10 < 2^w at room
  change start ≤ (ShrinkInput.widthBase X start+_+_+2*M)%(2^w)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

variable (pub : Fin 5 → Word w) (st : Word w) (mem : Memory w)

set_option maxHeartbeats 1000000 in
theorem term_values (reads : ShrinkBundlePlan.Reads X F i.val O pub st mem start T)
    (room : ShrinkInput.termEnd X start 10 < 2^w) :
    (I).motifs.eval pub st mem = (N : Word w) ∧ (I).termBase.eval pub st mem = term := by
  let z := ShrinkInput.plan X start
  let q := ShrinkRankSpace.Shape.collectBank z w
  let W := ShrinkInput.widthBase X start
  let ab := ShrinkWidthArena.abBase X q W
  let M := ShrinkTermRecipe.M X
  let R := ShrinkBundlePlan.termInputs i.val (a i) O
  have stopEq : ShrinkInput.stop X start = W+6*M+2*z.B := rfl
  change ShrinkInput.stop X start+2*M+M*10 < 2^w at room
  have fit : z.stop < 2^w := by change W < _; omega
  have hv := z.values T (ShrinkInput.placementBank X T start) Fintype.card_pos fit
  have hd : ab+2*M = ShrinkInput.stop X start := by
    rw [stopEq]
    change W+2*(z.B*(q 4).val)+2*(z.B*(q 4).val)+2*z.B+2*M = _
    rw [hv.stride]
    change W+2*M+2*M+2*z.B+2*M = _
    omega
  have data := ShrinkBundlePlan.term_input X reads fit
  refine ⟨(ShrinkTermRecipe.eval_count R X pub st mem data).trans
    (congrArg (fun z : ℕ => (z : Word w)) (ShrinkTermRecipe.count_card X)),?_⟩
  have value := ShrinkTermRecipe.eval_term R X pub st mem data
  change (I).termBase.eval pub st mem = ((ab+2*M+2*M : ℕ) : Word w) at value
  rw [hd] at value; exact value

theorem term_support {L : Layout} {first : ℕ} (h : ShrinkHeaderReads.Header i X T start L first mem)
    (entry : LevelFields.Entry L first pub st mem) (D : ℕ → Prop) (pitch : D (pub 1-1).val)
    (cells : ∀ n ≤ 60, D (levelStart L (first+i.val)+n)) :
    (I).motifs.ReadsFrom D pub st mem ∧ (I).termBase.ReadsFrom D pub st mem := by
  have field (n : ℕ) (hn : n ≤ 60) : (LevelFields.scalar i.val n).ReadsFrom D pub st mem :=
    GreedyVisit.scalar_support D L first i.val n entry pitch (cells n hn) ((Nat.add_le_add_left hn _).trans_lt h.room)
  have base : (O).ReadsFrom D pub st mem := field 60 le_rfl
  have inputs := BlockSlices.ab_supported i D pub st mem O O
    (fun j => field j.val (by have := j.isLt; omega)) base base
  have count : (I).motifs.ReadsFrom D pub st mem := ⟨inputs.rows,trivial⟩
  exact ⟨count,⟨⟨inputs.newWidths,trivial,count⟩,trivial,count⟩⟩

end CompressorRecords.ScorePackets

end

end VPVNP
end Computability
end OAI
