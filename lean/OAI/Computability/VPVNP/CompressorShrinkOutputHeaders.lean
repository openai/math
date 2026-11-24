import OAI.Computability.VPVNP.CompressorShrinkScheduledOutput

/-! # Scalar inputs for the final shrinking publication groups

The AB, surviving-width and slot visits preserve the controlling words and
both level headers. The final publishing calendar can therefore start from
the actual concatenation of Parts 5 through 8.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ScheduledShrink

open BurstRAM Compression ShrinkBlockInputs DescriptorSpace SourceOnline BlockPlanner
open ShrinkOutput SlotLevel ShrinkSlots
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {w g : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (base : Word w) (positions blocks round : ℕ)
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (Schedule.arity (Script.catalog prog)) base
local notation "first" => Script.levelsPerBlock prog*round
local notation "old" => first+i.val
local notation "next" => old+1
local notation "tab" => (fun j : Fin 6 => tableBase L old j)
local notation "T" => packedIncidence L w old (DemandRAM.oldCount X)
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "sh" => levelShape (b := b i) X
local notation "h" => ShrinkOutput.heads sh (SelectedArena.roleBase X term (10 : Word w)) (tab 3)
local notation "headBank" => PortRefresh.TraversalHeaders.HeadBank L
local notation "I" => BlockSlices.abInputs i (BlockProgram.arena B i.val 0) (BlockProgram.arena B i.val 1)

/-- The old fields, old and new public column addresses and low controller
words required after the selected slot group. -/
structure TailInputs (memory : Memory w) : Prop where
  header : ShrinkHeaderReads.Header i X T (tab 0) L first memory
  oldHeads : headBank old (DemandRAM.oldCount X) memory
  nextHeads : headBank next (actualCount sh) memory
  rows : memory (pt).rows.val = (directoryRows L : Word w)
  pitch : memory ((pt).directory-1).val = (levelWords L : Word w)

variable {B i X sel base positions blocks round}
variable {cap : ℕ} {m : Memory w} {ps₅ ps₆ ps₇ ps₈ : List (SourceOnline.Packet (BlockProgram.script B) w)} {r : TablesRun w}
local notation "out" => post m (((ps₅++ps₆)++ps₇)++ps₈)
local notation "mid" => post m ps₅

/-- Outside the slice and slot arenas and the copied successor incidence,
the appended four-part packet memory agrees with the output of Part 5. -/
theorem Output.frame (run : Output B i X sel base positions blocks round cap m ps₅ ps₆ ps₇ ps₈ r)
    (live : round < blocks) (sites : X.positions ≤ positions) (room : endAddress L < 2^w)
    (x : ℕ) (tables : x < tab 1 ∨ finish sh h ≤ x)
    (copy : x < incidenceStart L next ∨ incidenceStart L next+6*actualCount sh ≤ x) : out x = mid x := by
  rw [post_append,run.postWidth]
  exact scheduled_frame B i X sel base positions blocks round I mid mid cap r ps₈ live sites room run.tables
    run.slotReports x tables copy

set_option maxHeartbeats 1200000 in
theorem Output.tail_inputs (run : Output B i X sel base positions blocks round cap m ps₅ ps₆ ps₇ ps₈ r)
    (live : round < blocks) (sites : X.positions ≤ positions) (room : endAddress L < 2^w) :
    TailInputs B i X base positions blocks round out := by
  have liveOld : old < (L).levels := by
    change (S.steps+1)*round+i.val < 1+(S.steps+1)*blocks
    have upper := Nat.mul_le_mul_left (S.steps+1) live
    rw [Nat.mul_succ] at upper
    have hi := i.isLt
    omega
  let level : Fin (L).levels := ⟨old,liveOld⟩
  have oldRoom := BlockLevelFit.shrink (w := w) B base.val positions blocks level rfl i X sites room
  have slotBefore : finish sh h ≤ levelStart L next := oldRoom.2.2.2.2.2.2.1.next
  have headerSize : levelHeaderWords L = 66 := rfl
  have cut : levelStart L old+66 ≤ tab 0 := by
    change levelStart L old+66 ≤ levelStart L old+66+6*slotCapacity L+0*tableWords L
    omega
  have order : tab 0 ≤ tab 1 :=
    (Nat.le_add_right _ _).trans (tableEnd_le_tableBase L old (show (0 : Fin 6) < 1 by decide))
  have nextStart : tab 1 ≤ incidenceStart L next :=
    (Nat.le_add_right _ _).trans ((tableEnd_le_nextLevel L old (1 : Fin 6)).trans (Nat.le_add_right _ _))
  have low (x : ℕ) (hx : x < tab 1) : out x = mid x :=
    run.frame live sites room x (.inl hx) (.inl (hx.trans_le nextStart))
  have oldHead (n : ℕ) (hn : n < levelHeaderWords L) : out (levelStart L old+n) = mid (levelStart L old+n) :=
    low _ ((Nat.add_lt_add_left (hn.trans_eq headerSize) _).trans_le (cut.trans order))
  have nextHead (n : ℕ) (hn : n < levelHeaderWords L) : out (levelStart L next+n) = mid (levelStart L next+n) :=
    run.frame live sites room _ (.inr (slotBefore.trans (Nat.le_add_right _ _))) (.inl (Nat.add_lt_add_left hn _))
  have cells := Window.lowCells (A := prog) L base (BlockProgram.layout_arity B ..).symm rfl
    ((levelStart_mono L (Nat.zero_le (L).levels)).trans_lt room)
  have floor := (levelStart_mono L (Nat.zero_le old)).trans ((Nat.le_add_right _ 66).trans (cut.trans order))
  have below : levelStart L old+60 < tab 0 := (Nat.add_lt_add_left (by decide : 60 < 66) _).trans_le cut
  exact ⟨run.residents.header.keep_below below (fun x hx => low x (hx.trans_le order)),
    run.residents.oldHeads.keep oldHead,run.residents.nextHeads.keep nextHead,
    (low _ (cells.1.trans_le floor)).trans run.residents.rows,
    (low _ (cells.2.trans_le floor)).trans run.residents.pitch⟩

end CompressorRecords.ScheduledShrink

end

end VPVNP
end Computability
end OAI
