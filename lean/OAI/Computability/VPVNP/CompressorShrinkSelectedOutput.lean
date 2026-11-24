import OAI.Computability.VPVNP.CompressorRecordsShrinkOutputBuild
import OAI.Computability.VPVNP.CompressorShrinkResidentTerms
import OAI.Computability.VPVNP.CompressorShrinkOutputRetained
import OAI.Computability.VPVNP.CompressorSurvivingSweep

/-! # The fixed output workers after a selected shrinking pass

The four role programs read the layout bit, dense-to-absolute motif table,
and selected term fields from one post-selection memory. The slot passes
consume their absolute width rectangle. Their complete trace preserves
the preimage directory and gives the next state's six incidence columns.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkOutput

open Compression Compression.PackingData Compression.ShrinkMotif MotifBlocks MotifGrid
open BurstRAM SlotLevel ShrinkSlots ShrinkSliceSweep SurvivingNative
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {a b g w : ℕ} {δ : ℝ}
variable (B : S.Templates) (X : State a (packingLaneBits a g))
variable (ready : Ready (2^a) (Shrink.colors a) (2^b) δ) (sel : SelectedScore.Selection B X)
variable (term stride abs : Word w)

/-- Word address of the chosen layout bit, two cells after the start of the score arena. -/
abbrev layoutWord := Fin.ofNat (2^w) (SelectedArena.origin X term stride+2)

local notation "sh" => levelShape (b := b) X
local notation "role" => SelectedArena.roleBase X term stride
local notation "keepEnd" => SelectedFinish.stop X term stride
local notation "cutoff" => widthBase X term.val stride.val role keepEnd
local notation "T" => splitBank (b := b) X B.shrink sel term stride.val role keepEnd
local notation "side" => SelectedFinish.chosen B X sel
local notation "sz" => selected X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex) T B.shrink X.packingWidth sel

local notation "bankAt" => splitBank (b := b) X B.shrink sel term stride.val role
local notation "sizesAt" => fun floor : ℕ => selected X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex)
  (bankAt floor) B.shrink X.packingWidth sel

/-- The width-scan traces for the four surviving roles, their output memory, and the subsequent
construction of the successor’s slot tables. -/
structure Passes (w : ℕ) where
  /-- Lists of native width reports grouped by surviving role, in the order of the four role
  sweeps. -/
  widthRows : List (List (Report w))
  /-- The memory handed from the four role width sweeps to the slot-table construction. -/
  postWidths : Memory w
  /-- Construction traces that consume the role widths and build the successor’s slot and
  incidence tables. -/
  slots : Build.Construction w

/-- The full output trace, with the role width reports flattened in sweep order and followed by
all slot-construction reports. -/
def Passes.reports (p : Passes w) := p.widthRows.flatten++p.slots.all
/-- Memory obtained by replaying the slot construction from the memory produced by the width
sweeps. -/
def Passes.final (p : Passes w) := p.slots.final p.postWidths

/-- The actual fixed controls and final readback on one selected branch. -/
structure Complete (cap : ℕ) (mem : Memory w) (p : Passes w) (floor : ℕ := keepEnd)
    (slotStart : ℕ := (slotHeads (b := b) X term.val stride.val role floor).role) : Prop where
  sweep : SurvivingPass.Roles (bankAt floor) (sizesAt floor) (fun t => program (bankAt floor) t abs (layoutWord X term stride)) (fun _ => cap)
    (fun t => SurvivingNative.Site (bankAt floor) t abs (layoutWord X term stride)) (List.finRange 4) mem p.postWidths p.widthRows
  construction : Constructed X B.shrink ready sel term stride.val role floor mem p.postWidths p.slots slotStart
  preimages : ShrinkPreimages.Directory X side (SelectedFinish.counts X term stride) (SelectedFinish.rows X term stride) p.final
  directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber abs p.final
  replay : after mem (eventLog p.reports) = p.final
  probes : RAMBuckets.cost Report.probes p.reports = 18*(motifCount X*(bankAt floor).stride)+slotProbes sh
  rowCounts : p.widthRows.map List.length = List.ofFn (fun t => motifCount X*(bankAt floor).subdiv t)

set_option maxHeartbeats 1800000 in
/-- Execute the same fixed controls at the width-table and slot-table heads
chosen by the block calendar. A gap between the two tables is permitted. -/
theorem build_at (input : Memory w) (floor slotStart : ℕ) (keepBefore : keepEnd ≤ floor)
    (wide : 10 ≤ stride.val) (hw : FitsWords (b := b) X B.shrink term stride.val role floor)
    (slotAfter : (bankAt floor).last ≤ slotStart) (slotRoom : finish sh (heads sh role slotStart) < 2^w)
    (absBefore : abs.val+motifCount X ≤ keepEnd)
    (directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber abs input)
    (terms : Terms X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex) (bankAt floor) B.shrink X.packingWidth sel input)
    (roles : DemandRAM.RoleColumns X side role input)
    (sideWord : input (SelectedArena.origin X term stride+2) = ((side).toNat : Word w))
    (preimages : ShrinkPreimages.Directory X side (SelectedFinish.counts X term stride) (SelectedFinish.rows X term stride) input)
    (cap : ℕ) (fuel : SurvivingNative.ops.length < cap) :
    ∃ result : Passes w, Complete B X ready sel term stride abs cap input result floor slotStart := by
  let fit := fits X B.shrink sel term stride.val role floor ready wide hw.room
  have lower := keepBefore.trans (retained_room X term stride.val role floor)
  have upper := (width_le_slots (b := b) X term stride.val role floor).trans (slots_le_stop X term stride.val role floor)
  have idFit := absBefore.trans (lower.trans (upper.trans hw.room.le))
  have idLo (j : Fin (motifCount X)) : abs.val+j.val < widthBase X term.val stride.val role floor := (Nat.add_lt_add_left j.isLt _).trans_le (absBefore.trans lower)
  have sideLo : SelectedArena.origin X term stride+2 < keepEnd := by
    unfold SelectedFinish.stop SelectedFinish.rowStart SelectedFinish.countStart SelectedArena.endAddr
      SelectedArena.roleBase SelectedArena.placementBase
    omega
  have sideEq : (layoutWord X term stride).val = SelectedArena.origin X term stride+2 :=
    Nat.mod_eq_of_lt (sideLo.trans_le (lower.trans (upper.trans hw.room.le)))
  have chosenWord : (input (layoutWord X term stride).val).val = (bankAt floor).layout.toNat := by
    rw [sideEq]
    have hsmall : (side).toNat ≤ 1 := by cases side <;> decide
    have bitFit : (side).toNat < 2^w := hsmall.trans_lt (by have := fit.roles; omega)
    exact (congrArg Fin.val sideWord).trans (Nat.mod_eq_of_lt bitFit)
  have absolute := directory_for_selected B.shrink X term abs stride.val (widthBase X term.val stride.val role floor) (sh).subdivisions sel input directory
  obtain ⟨out,rows,walk,_,_,images,values,frame,lengths,_,cost⟩ :=
    SurvivingSweep.graph X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex) X.baseIndex
      (bitWordFinEquiv (Shrink.J a)) (bitWordFinEquiv g) (bankAt floor) B.shrink X.packingWidth sel
      rfl fit (Nat.mod_eq_of_lt hw.selector) (supply_fit X B.shrink sel term stride.val role floor hw)
      abs (layoutWord X term stride) idFit (fun i j => (bankAt floor).rowOutside fit i _ (.inl (idLo j)))
      (fun i => (bankAt floor).rowOutside fit i _ (.inl (sideEq ▸ sideLo.trans_le lower))) cap fuel input absolute chosenWord terms
  obtain ⟨slot,constructed⟩ := finish_after_sweep_at X B.shrink ready sel term stride.val role floor slotStart slotAfter slotRoom wide hw input out
    roles images values frame
  let result : Passes w := ⟨rows,out,slot⟩
  refine ⟨result,⟨walk,constructed,?_,?_,?_,?_,lengths⟩⟩
  · exact preimages_retained X term stride preimages (fun j hj => constructed.frame j (.inl (hj.trans_le lower)))
  · intro j
    exact (congrArg Fin.val (constructed.frame _ (.inl (idLo j)))).trans (directory j)
  · change after input (eventLog (rows.flatten++slot.all)) = slot.final out
    rw [show after input (eventLog (rows.flatten++slot.all)) = after (after input (eventLog rows.flatten)) (eventLog slot.all) by
      simp only [after,eventLog,List.flatMap_append,List.foldl_append],walk.replay,slot.final_eq]
  · exact (RAMBuckets.cost_append Report.probes rows.flatten slot.all).trans (congrArg₂ (·+·) cost constructed.probes)

set_option maxHeartbeats 1800000 in
/-- The width and ordered-slot arrays are produced from the earlier selected
stage and the physical absolute-ID table. The layout bit remains at its
score-comparison address through the preimage and output passes. -/
theorem build_selected (selectors : Word w) (p₀ : Fin 14 → Word w) (mem : Memory w)
    (p : SelectedStage.Passes w) (q : SelectedFinish.Passes w)
    (chosen : SelectedFinish.Built B X term stride selectors p₀ sel mem p q)
    (wide : 10 ≤ stride.val) (hw : FitsWords (b := b) X B.shrink term stride.val role keepEnd)
    (absBefore : abs.val+motifCount X ≤ keepEnd)
    (directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber abs (q.final (p.final mem)))
    (cap : ℕ) (fuel : SurvivingNative.ops.length < cap) :
    ∃ result : Passes w, Complete B X ready sel term stride abs cap (q.final (p.final mem)) result :=
  build_at B X ready sel term stride abs (q.final (p.final mem)) keepEnd
    (slotHeads (b := b) X term.val stride.val role keepEnd).role le_rfl wide hw le_rfl hw.room absBefore directory
    (resident_terms (b := b) B X term stride selectors role keepEnd sel _ chosen.terms)
    chosen.roles chosen.chosenCell chosen.raw.directory cap fuel

end CompressorRecords.ShrinkOutput

end

end VPVNP
end Computability
end OAI
