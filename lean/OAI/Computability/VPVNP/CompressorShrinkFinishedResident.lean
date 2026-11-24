import OAI.Computability.VPVNP.CompressorShrinkScheduledFinish
import OAI.Computability.VPVNP.CompressorShrinkOutputHeaders
import OAI.Computability.VPVNP.CompressorShrinkSelectedEmission
import OAI.Computability.VPVNP.CompressorCompiledResident
import OAI.Computability.VPVNP.CompressorSelectedPayloadFrames
import OAI.Computability.VPVNP.PairShrinkResidentSourceCapture
import OAI.Computability.VPVNP.PairShrinkResidentHeaderWords

/-! # The complete retained state of a scheduled shrinking pass

The selected geometry produces the ordered preimages. The next four groups
retain that table and install the successor incidence. The final three
publications record the placement operands and the parser data of this
selected occurrence in the same memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ShrinkScheduledFinish

open BurstRAM Compression DescriptorSpace BlockPlanner SourceOnline BlockHeaderRun
open ShrinkBlockInputs SelectedDirectoryHistory PairSimulation.TraversalRows
open PairSimulation.TraversalRoles
open PairSimulation.LocalHistory PairSimulation SelectedPayloadHistory
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
variable {f : B.Entry → R} {hf : B.IsSolution f} {i : Fin S.steps} {w g : ℕ}
variable {X : State (a i) (packingLaneBits (a i) g)} {sel : SelectedScore.Selection B X}
variable {bits : List Bool}
variable {base : Word w} {positions blocks round fuel cap n : ℕ}
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "fst" => Script.levelsPerBlock scr * round
local notation "cur" => fst + i.val
local notation "head" => levelStart L cur
local notation "nextHead" => levelStart L (cur + 1)
local notation "tab" => (fun j : Fin 6 => tableBase L cur j)
local notation "T" => packedIncidence L w cur (DemandRAM.oldCount X)
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "v" => shrinkLevel B f hf i X sel bits

variable {raw : Memory w}
variable {p : ShrinkBranch.Prefix X
  (packedIncidence (BlockProgram.layout B base.val positions blocks) w
    ((S.steps + 1) * round + i.val) (DemandRAM.oldCount X))
  (tableBase (BlockProgram.layout B base.val positions blocks)
    ((S.steps + 1) * round + i.val) (0 : Fin 6)) fuel raw}
variable (branch : ShrinkBranch.Selected B X
  (packedIncidence (BlockProgram.layout B base.val positions blocks) w
    ((S.steps + 1) * round + i.val) (DemandRAM.oldCount X))
  (tableBase (BlockProgram.layout B base.val positions blocks)
    ((S.steps + 1) * round + i.val) (0 : Fin 6))
  10 (B.shrink.selectorBits : Word w) fuel raw p sel)
variable {ps₅ ps₆ ps₇ ps₈ metadata tail : List (Packet (BlockProgram.script B) w)}
variable {r : ShrinkOutput.TablesRun w}
variable (z : Finish B i X sel base positions blocks round cap
  branch.beforeOutput ps₅ ps₆ ps₇ ps₈ metadata tail r)
variable (live : round < blocks) (size : X.positions ≤ positions)
  (fit : endAddress (BlockProgram.layout B base.val positions blocks) < 2 ^ w)
local notation "mid" => post branch.beforeOutput (((ps₅ ++ ps₆) ++ ps₇) ++ ps₈)
local notation "out" => post mid tail

include z live size fit in
private theorem Finish.before_tail (x : ℕ)
    (safe : (x < tab 1 ∧ (x < head + 30 ∨ head + 36 ≤ x)) ∨
      (nextHead ≤ x ∧ x < incidenceStart L (cur + 1))) : mid x = branch.beforeOutput x := by
  have bnd := ShrinkResidentSources.bounds B i X base positions blocks round live size fit
  have beforeNext : tab 1 ≤ nextHead := (Nat.le_add_right ..).trans
    (tableEnd_le_nextLevel L cur (1 : Fin 6))
  have beforeFive : tab 1 ≤ tab 5 := (Nat.le_add_right ..).trans
    (tableEnd_le_tableBase L cur (show (1 : Fin 6) < 5 by decide))
  have headerBefore : head + 66 ≤ nextHead := by
    have h : head + 66 ≤ tab 1 := by
      change head + 66 ≤ head + 66 + 6 * slotCapacity L + 1 * tableWords L
      omega
    exact h.trans beforeNext
  rcases safe with ⟨hi, h⟩|⟨lo, hi⟩
  · apply (z.output.frame live size fit x (.inl hi)
    (.inl ((hi.trans_le beforeNext).trans_le (Nat.le_add_right ..)))).trans
    apply z.output.residents.preserved
    rintro (d|d)
    · exact (hi.trans_le beforeFive).not_ge d.1
    · change head + 30 ≤ x ∧ x < head + 36 at d
      omega
  · apply (z.output.frame live size fit x (.inr (bnd.slotEnd.trans lo)) (.inl hi)).trans
    apply z.output.residents.preserved
    rintro (d|d)
    · exact (d.2.trans_le bnd.residentEnd).not_ge lo
    · change head + 30 ≤ x ∧ x < head + 36 at d
      omega

include z live size fit in
/-- Actual preimage collection, physical slot frame and metadata reports
give the directory in the final memory, including its successor's DFS base. -/
def Finish.selectedEmission (length : mid (levelStart L 0 + 29) = (n : Word w)) :
    Emission L cur v mid out := by
  have bnd := ShrinkResidentSources.bounds B i X base positions blocks round live size fit
  have ins := z.output.tail_inputs live size fit
  have nextFit := (levelStart_mono L bnd.nextLive.le).trans_lt fit
  have beforeNext : tab 1 ≤ nextHead := (Nat.le_add_right ..).trans
    (tableEnd_le_nextLevel L cur (1 : Fin 6))
  have headerBefore : head + 66 ≤ tab 0 := by
    change head + 66 ≤ head + 66 + 6 * slotCapacity L + 0 * tableWords L
    omega
  apply z.published.selectedEmission T branch.postTerm.geometry
    (bnd.selectedBefore.trans beforeNext)
    nextFit bnd.termRoom _ ins.header ins.pitch ins.rows length
  intro x lo hi
  change tab 0 ≤ x at lo
  exact z.before_tail branch live size fit x
    (.inl ⟨hi.trans_le bnd.selectedBefore, .inr (by omega)⟩)

include z live size fit in
/-- Starting at the actual substep, append one occurrence to both the DFS
history and the retained parser snapshots. The geometry frame is the one
returned by the first 36 calendar visits. -/
theorem Finish.advance {initial : TaggedLayer} {initialFrame : Fin 8 → Word w}
    {past : List (SelectedLevel B f hf)} {before : Memory w}
    (old new : Fin (L).levels) (oldAt : old.val = cur) (next : old.val + 1 = new.val)
      (index : past.length = old.val)
    (stored : CompiledResident.resident B f hf base positions blocks n initial initialFrame
      past X before)
    (sub : Substep v L old new (by change 6 ≤ 54; decide) before)
    (geometry : ∀ x, x < tab 0 ∨ nextHead ≤ x
      → branch.beforeOutput x = finalMemory v L old new before x) :
    CompiledResident.resident B f hf base positions blocks n initial initialFrame
      (past ++ [v]) ((v).pass.next (v).term) out := by
  have newAt : new.val = cur + 1 := by omega
  have ix := index.trans oldAt
  have floor := levelStart_mono L (Nat.zero_le cur)
  have cut : head + 66 ≤ tab 0 := by
    change head + 66 ≤ head + 66 + 6 * slotCapacity L + 0 * tableWords L
    omega
  have order : tab 0 ≤ tab 1 := (Nat.le_add_right ..).trans
    (tableEnd_le_tableBase L cur (show (0 : Fin 6) < 1 by decide))
  have nextBound : levelStart L (cur + 1) ≤ incidenceStart L (cur + 1) := Nat.le_add_right ..
  have through (x : ℕ) (hx : x < head + 30 ∨ CurrentGraph.graphCell L (cur + 1) x) :
      mid x = finalMemory v L old new before x := by
    rcases hx with low | h
    · exact (z.before_tail branch live size fit x (.inl ⟨by omega, .inl low⟩)).trans
        (geometry x (.inl (by omega)))
    · have a : nextHead ≤ x ∧ x < incidenceStart L (cur + 1) := by
        rcases h with h|h
        · change _ ∧ x < nextHead + 66; omega
        · exact ⟨(Nat.le_add_right ..).trans h.1, h.2⟩
      exact (z.before_tail branch live size fit x (.inr a)).trans (geometry x (.inr a.1))
  have earlier : InputFrame L cur before (finalMemory v L old new before) :=
    oldAt ▸ InputFrame.substep sub next
  have post8Frame : InputFrame L cur (finalMemory v L old new before) mid := by
    refine ⟨fun x _ hi => through x (.inl (by omega)), ?_⟩
    intro x hx
    obtain ⟨lo, hi⟩ := hx
    change head + 54 ≤ x at lo
    have cutEq : arrayBase L cur = tab 0 := by change _ = _ + 0 * _; omega
    rw [cutEq] at hi
    exact ((z.before_tail branch live size fit x (.inl ⟨hi.trans_le order, .inr (by omega)⟩)).trans
      (geometry x (.inl hi))).symm
  have stable := (earlier.trans post8Frame).trans (InputFrame.shrinkTail z.published)
  have length : mid (levelStart L 0 + 29) = (n : Word w) := by
    apply (through _ (.inl (by omega))).trans
    apply (sub.firstScalarTail v next 29 (by decide) (by change 29 < 54; decide)).trans
    exact (Fin.cast_val_eq_self _).symm.trans
      (congrArg (fun x : ℕ => (x : Word w)) stored.1.2.1.startup.length)
  have bnd := ShrinkResidentSources.bounds B i X base positions blocks round live size fit
  have ins := z.output.tail_inputs live size fit
  have counts := (ShrinkSlots.next_counts X B.shrink (S.shrink i) sel).2
  have countEq : IncidenceDirectory.slotCount ((v).pass.next (v).term) =
      ShrinkSlots.actualCount (ShrinkSlots.levelShape (b := b i) X) := counts
  have current := z.published.advance old new oldAt next index stored.1 sub fit
    (countEq.symm ▸ bnd.nextCapacity) (by
      rw [newAt, countEq]
      exact z.output.readbacks.incidence)
    (z.selectedEmission branch live size fit length) (fun x _ h => through x h)
  apply DetailedResident.append stored current
  · rw [ix]
    change CompiledResident.ShrinkPayload B base positions blocks n cur i X sel out
    refine ⟨bnd, ShrinkResidentSources.Data.capture branch z.output z.published live size fit,
      ShrinkResidentHeaders.Words.of_tail z.published ins.header ins.oldHeads ins.nextHeads
        z.output.readbacks ins.rows ins.pitch length live size fit,
      SelectedChildDirectory.Stored.of_shrink_tail z.published ins.header ins.pitch
        bnd.termRoom ins.rows length,
      ⟨ShrinkInput.demandHead (w := w) X (tab 0), fuel, p.beforeTerm, branch.terms, ?_⟩⟩
    have ten : (10 : Word w).val = 10 :=
      Nat.mod_eq_of_lt (show (10 : ℕ) < 2 ^ w by have := ins.header.room; omega)
    have tr := branch.termRun
    rw [ten] at tr
    exact tr
  · simpa only [ix] using stable.earlier
  · simpa only [ix] using stable.graph

end CompressorRecords.ShrinkScheduledFinish

end

end VPVNP
end Computability
end OAI
