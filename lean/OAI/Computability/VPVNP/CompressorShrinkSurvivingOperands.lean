import OAI.Computability.VPVNP.CompressorShrinkSelectedReadback
import OAI.Computability.VPVNP.CompressorShrinkAllocatedTables
import OAI.Computability.VPVNP.CompressorShrinkBundleAbsolute

/-! # Operands of the four surviving-role visits

The planner computes the address of the chosen layout from the old level
header. The native worker loads the layout at this address on each call.
All reads made while preparing the packet lie below table zero, including
the pointer to the width rectangle in table two.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkSurvivingOperands

open BurstRAM Compression BlockPlanner PhaseRecipe DescriptorSpace ShrinkBlockInputs ShrinkSliceSweep
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (inc : IncidenceDirectory w) (start : ℕ)
variable (sel : SelectedScore.Selection B X) (width : ℕ)
variable (pub : Fin 5 → Word w) (st : Word w) (m : Memory w)
local notation "F" => BlockProgram.geometry B
local notation "origin" => BlockProgram.arena B i.val 0
local notation "widthArena" => BlockProgram.arena B i.val 2
local notation "chosen" => selectedInputs B F i origin
local notation "heads" => BlockSlices.survivingHeads B F i origin widthArena
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "step" => (10 : Word w)
local notation "score" => (SelectedArena.origin X term step + 2 : ℕ)
local notation "bank" => ShrinkOutput.splitBank (b := b i) X B.shrink sel term
  (Fin.val step) (SelectedArena.roleBase X term step) width
local notation "abs" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X start) w

/-- The published scalar and table cells supply the exact stop and all eleven
native operands for each role. The support bound allows reuse after the AB
and surviving scans write in later tables. -/
theorem fields {L : Layout} {first : ℕ}
    (header : ShrinkHeaderReads.Header i X inc start L first m)
    (entry : LevelFields.Entry L first pub st m) (termRoom : ShrinkInput.termEnd X start 10 < 2 ^ w)
    (widthAfter : SelectedFinish.stop X term step ≤ width)
    (widthCell : m (levelStart L (first + i.val) + 62) = (width : Word w))
    (headerBelow : levelStart L (first + i.val) + 62 < start)
    (pitchLo : (pub 1 - 1).val < start) (D : ℕ → Prop) (pitchD : D (pub 1 - 1).val)
    (dataD : ∀ x, levelStart L 0 ≤ x → D x) (role : Fin 4) :
    let v := SurvivingNative.visits (slotTemplate i).subdivisions heads role
    (v.initial.eval pub st m = 0 ∧
      v.stop.eval pub st m = ((ShrinkOutput.motifCount X * (bank).subdiv role : ℕ) : Word w) ∧
      (fun j => (v.params j).eval pub st m) = SurvivingNative.params bank role abs (score : Word w)) ∧
      HeaderOperands.Supported (fun x => D x ∧ x < start) pub st m v := by
  intro v
  let R := fun x => D x ∧ x < start
  have firstLo := levelStart_mono L (Nat.zero_le (first+i.val))
  have startFit := (ScorePackets.start_le_term i X start termRoom).trans_lt (term).isLt
  have cell (n : ℕ) (hn : n ≤ 62) : R (levelStart L (first+i.val)+n) :=
    ⟨dataD _ (firstLo.trans (Nat.le_add_right ..)),by omega⟩
  have pitch : R (pub 1 - 1).val := ⟨pitchD,pitchLo⟩
  have ten : 10 < 2 ^ w := by have := header.room; omega
  obtain ⟨read,support⟩ := SelectedTailPackets.header_values B i X inc start pub st m header entry
    termRoom ten R pitch (fun n hn => cell n (by omega))
  have absolute := (ShrinkBundlePlan.head_values X (header.reads B entry)).absoluteCD
  have widthEq := ShrinkOutput.width_at_eq i X term step width widthAfter
  have widthValue : (widthArena).eval pub st m = (width : Word w) :=
    (LevelFields.eval_scalar entry i.val 62 (by omega)).trans widthCell
  have motifEq : ShrinkOutput.motifCount X = SelectedArena.motifs X := ShrinkTermRecipe.count_card X
  have scoreValue : (SelectedPlan.layoutCell chosen).eval pub st m = (score : Word w) := by
    change (SelectedPlan.scoreBase chosen).eval pub st m + 2 = _
    rw [SelectedPlan.score_head chosen X _ inc term pub st m read,Nat.cast_add,Nat.cast_ofNat]
    rfl
  have intervalValue : (heads).intervalBase.eval pub st m = ((bank).widthEnd : Word w) := by
    change (widthArena).eval pub st m +
      (4*(chosen).oldSlots.eval pub st m)*(BlockSlices.subdivisionSum i : Word w) =
      ((ShrinkOutput.widthBase X (term).val (step).val (SelectedArena.roleBase X term step) width +
        (DemandRAM.absoluteCount X*4)*BlockSlices.subdivisionSum i : ℕ) : Word w)
    rw [widthValue,widthEq,read.slots,DemandRAM.count_eq X]
    push_cast
    ring
  constructor
  · apply SurvivingNative.visit_fields bank heads role pub st abs (score : Word w) m
    · exact read.motifs.trans (congrArg (fun n : ℕ => (n : Word w)) motifEq.symm)
    · exact read.term.trans (Fin.cast_val_eq_self _).symm
    · exact (Fin.cast_val_eq_self _).symm
    · exact absolute
    · exact scoreValue
    · rfl
    · exact widthValue.trans (congrArg (fun n : ℕ => (n : Word w)) widthEq.symm)
    · exact intervalValue
  · let safe := Expr.ReadsFrom R pub st m
    have widthRead : safe widthArena :=
      GreedyVisit.scalar_support R L first i.val 62 entry pitch (cell 62 le_rfl) (by omega)
    have absStage := ShrinkBundlePackets.expr_reads B i header entry R pitch
      (fun n hn => cell n (by omega)) .absolute
    have cdStage := ShrinkBundlePackets.expr_reads B i header entry R pitch
      (fun n hn => cell n (by omega)) .motifPrefix
    have absRead : safe (heads).absolute := ⟨absStage.params (4 : Fin 7),cdStage.stop⟩
    have layoutRead : safe (heads).layout := ⟨⟨support.term,support.motifs,trivial⟩,trivial⟩
    have intervalRead : safe (heads).intervalBase := ⟨widthRead,⟨trivial,support.slots⟩,trivial⟩
    refine ⟨trivial,⟨support.motifs,trivial⟩,?_⟩
    intro j
    change Fin 11 at j
    fin_cases j
    exacts [True.intro,True.intro,support.term,True.intro,absRead,layoutRead,True.intro,widthRead,
      True.intro,intervalRead,True.intro]

end CompressorRecords.ShrinkSurvivingOperands

end

end VPVNP
end Computability
end OAI
