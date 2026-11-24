import OAI.Computability.VPVNP.PairShrinkResidentHeaders
import OAI.Computability.VPVNP.PairShrinkPublishedSupplyWords

/-! # Chronological retention of a shrinking level's resident header -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkResidentHeaders

open BurstRAM Compression CompressorRecords DescriptorSpace BlockPlanner SourceOnline ShrinkSlots
open SourceTransport ShrinkBlockInputs Schedule
open scoped Fin.CommRing

variable {K : Type*} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
variable (i : Fin S.steps) {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g))
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
variable (sel : SelectedScore.Selection B X) (base : Word w) (positions blocks cur n : ℕ)
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "here" => levelStart L cur
local notation "next" => levelStart L (cur + 1)
local notation "tab" => (fun j : Fin 6 ↦ tableBase L cur j)
local notation "T" => packedIncidence L w cur (DemandRAM.oldCount X)
local notation "sh" => levelShape (b := b i) X
local notation "H" => ShrinkResidentLayout.layout X (tab 5)

/-- Header values retained in the selected pass history. The successor's layer base
and descriptor pitch come from the DFS directory history and the next pass. -/
structure Words (mem : Memory w) : Prop where
  level : ShrinkCallHeader.Level X B.shrink sel (here : Word w) mem T (tab 0)
    (mem (here + 14)).val (B.recordLimit + 2) (tab 1)
  length : mem (here + 17) = (n : Word w)
  residentHeads : ∀ j : Fin 6, mem (here + (30 + j.val)) =
    (ShrinkResidentsPlan.headValues H j : Word w)
  supply : ShrinkPublishedSupplyWords.Stored B i X sel base positions blocks cur mem
  successor : PortRefresh.TraversalHeaders.HeadBank L (cur + 1) (actualCount sh) mem
  oldRoom : here + 65 < 2 ^ w
  nextRoom : next + 65 < 2 ^ w

variable {B i X sel base positions blocks cur n}
variable {m out : Memory w}

private theorem head_cast (h j : ℕ) (fit : h + j < 2 ^ w) :
    (((h : Word w) + (j : Word w))).val = h + j := by
  rw [← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt fit]

theorem Words.strideWord (p : Words B i X sel base positions blocks cur n m) :
    m (here + 15) = ((B.recordLimit + 2 : ℕ) : Word w) := by
  have room := p.oldRoom
  have h := head_cast (w := w) (here) 15 (by omega)
  exact (congrArg m h).symm.trans p.level.rowStride

private theorem before_next : here + 66 ≤ next := by
  have sz : levelHeaderWords L = 66 := rfl
  simp only [levelStart, Nat.succ_mul, levelWords, sz]
  omega

open private HeadBank.keep_pointers from OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders

/-- Transport the parser's old-header readbacks and all successor pointer
words from the producer snapshot along the actual selected history frame. -/
theorem Words.transfer (p : Words B i X sel base positions blocks cur n m)
    (same : Agree (SelectedPayloadHistory.Cells L cur) m out) :
    Words B i X sel base positions blocks cur n out := by
  have gap : here + 66 ≤ next := before_next
  have natAt (j : ℕ) (small : j < 66) : out (here + j) = m (here + j) :=
    (same _ (.inl ⟨Nat.le_add_right .., by omega⟩)).symm
  have takeWord (j : ℕ) (small : j < 66) (v : Word w)
      (word : m ((here : Word w) + (j : Word w)).val = v) :
      out ((here : Word w) + (j : Word w)).val = v := by
    have room := p.oldRoom
    rw [head_cast (here) j (by omega)] at *
    exact (natAt j small).trans word
  have kept := p.level
  refine ⟨?_, (natAt 17 (by decide)).trans p.length,
    fun j ↦ (natAt _ (by have := j.isLt; omega)).trans (p.residentHeads j), ?_, ?_,
    p.oldRoom, p.nextRoom⟩
  · rw [natAt 14 (by decide)]
    exact ⟨takeWord 0 (by decide) _ kept.vertices, takeWord 1 (by decide) _ kept.degree,
      takeWord 2 (by decide) _ kept.lanes, takeWord 3 (by decide) _ kept.residual,
      takeWord 14 (by decide) _ kept.oldLayer, takeWord 15 (by decide) _ kept.rowStride,
      takeWord 36 (by decide) _ kept.termHead, takeWord 37 (by decide) _ kept.termStride,
      takeWord 38 (by decide) _ kept.layout, takeWord 43 (by decide) _ kept.abBank,
      takeWord 44 (by decide) _ kept.owner, takeWord 45 (by decide) _ kept.rankHead,
      takeWord 46 (by decide) _ kept.ids, takeWord 47 (by decide) _ kept.demandHead,
      takeWord 57 (by decide) _ kept.actualOut, takeWord 58 (by decide) _ kept.actualIn,
      takeWord 59 (by decide) _ kept.width⟩
  · exact ⟨(natAt 39 (by decide)).trans p.supply.absolute,
      (natAt 40 (by decide)).trans p.supply.successor,
      (natAt 41 (by decide)).trans p.supply.inverse,
      (natAt 42 (by decide)).trans p.supply.interval⟩
  · apply HeadBank.keep_pointers p.successor
    intro j lo hi
    apply (same _ (.inr ?_)).symm
    exact ⟨Nat.add_le_add_left lo _, (Nat.add_lt_add_left hi _).trans_le (Nat.le_add_right ..)⟩

section Production

variable {t cap : ℕ}
local notation "prog" => BlockProgram.script B
local notation "start" => Script.levelsPerBlock prog * t
local notation "atOld" => start + i.val
local notation "oldHead" => levelStart L atOld
local notation "newHead" => levelStart L (atOld + 1)
local notation "tableAt" => (fun j : Fin 6 ↦ tableBase L atOld j)
local notation "oldInc" => packedIncidence L w atOld (DemandRAM.oldCount X)
local notation "pt" => Workspace.ports (arity (Script.catalog prog)) base
local notation "pub" => Ports.data pt
variable {ms ps : List (SourceOnline.Packet (BlockProgram.script B) w)}

/-- Capture the old and successor pointer words from the actual three terminal
publication groups. The successor pitch is supplied by the next selected pass. -/
theorem Words.of_tail (tail : ShrinkScheduledTail.Result B base positions blocks t cap i X m ms ps)
    (header : ShrinkHeaderReads.Header i X oldInc (tableAt 0) L start m)
    (oldBank : PortRefresh.TraversalHeaders.HeadBank L atOld (DemandRAM.oldCount X) m)
    (nextBank : PortRefresh.TraversalHeaders.HeadBank L (atOld + 1) (actualCount sh) m)
    (read : ShrinkOutput.ScheduledReadbacks B i X sel base positions blocks t oldInc m)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m (pub 1 - 1).val = (levelWords L : Word w))
    (initial : m (levelStart L 0 + 29) = (n : Word w))
    (live : t < blocks) (size : X.positions ≤ positions) (fit : endAddress L < 2 ^ w) :
    Words B i X sel base positions blocks atOld n (post m ps) := by
  have room := PublishedHeads.level_room B base positions blocks t i.val live i.isLt.le fit
  have newRoom := PublishedHeads.level_room B base positions blocks t (i.val + 1) live i.isLt fit
  have gap : oldHead + 66 ≤ newHead := before_next
  have low := levelStart_mono L (Nat.zero_le atOld)
  have eqn : start + (i.val + 1) = atOld + 1 := (Nat.add_assoc ..).symm
  rw [eqn] at newRoom
  have stable (j : ℕ) (small : j < 66) (metadata : j < 15 ∨ 27 ≤ j)
      (published : j < 36 ∨ 54 ≤ j) : post m ps (oldHead + j) = m (oldHead + j) := by
    apply tail.outside
    · omega
    · omega
    · rw [eqn]; omega
    · rw [eqn]; omega
  refine ⟨?_, lengthWord tail n rows (by omega) initial,
    fun j ↦ (stable _ (by have := j.isLt; omega) (.inr (by omega))
      (.inl (by have := j.isLt; omega))).trans (read.hidden.heads j),
    ShrinkPublishedSupplyWords.of_tail B i X sel base positions blocks t oldInc header
      (fun j ↦ by
        have h := oldBank.tables j
        change m (oldHead + 60 + j.val) = _ at h
        rw [← Nat.add_assoc]
        exact h)
      pitch live size fit tail, ?_, by omega, by omega⟩
  · rw [stable 14 (by decide) (by decide) (by decide)]
    exact oldLevel tail live size fit header oldBank pitch read
  · apply HeadBank.keep_pointers nextBank
    intro j lo _
    apply tail.next_data
    rw [eqn]
    change 54 ≤ j at lo
    omega

end Production

end PairSimulation.ShrinkResidentHeaders

end

end VPVNP
end Computability
end OAI
