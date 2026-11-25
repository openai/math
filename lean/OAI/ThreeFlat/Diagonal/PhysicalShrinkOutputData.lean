import OAI.ThreeFlat.Diagonal.CompressorIncidentProbe
import OAI.ThreeFlat.Diagonal.ShrinkPublishedHalves
import OAI.ThreeFlat.Diagonal.PhysicalShrinkCommit
import OAI.ThreeFlat.Diagonal.ShrinkDescriptorPublication
import OAI.ThreeFlat.Diagonal.PhysicalShrinkActualOutput
import OAI.ThreeFlat.Diagonal.PhysicalShrinkOutputBounds

namespace OAI
/-! # The stored output of the native shrink writer -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement Native.Graph
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav
open scoped Classical Fin.NatCast
noncomputable section
open private palette_two from OAI.ThreeFlat.Diagonal.PhysicalShrinkPre
open private rawConditions tag_size from OAI.ThreeFlat.Diagonal.PhysicalShrinkSuccessor
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "Q" => shrinkBinaryFamily T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "N" => Fintype.card (State.Base (shrinkRecordState s rem A))
local notation "P" => shrinkRecordPacking s rem A
local notation "oldDegree" => (2^s : ℕ)
local notation "palette" => (2*oldDegree+1 : ℕ)
local notation "hc" => palette_two s
local notation "good" => rawConditions s rem (shrinkRecordState s rem A)
local notation "S" => shrinkStage s D
local notation "tagCount" => tagBits oldDegree
local notation "x" => dims S N tagCount rem
local notation "stagePad" => PhysicalShrink.padding palette oldDegree D
local notation "prior" => shrinkRecordWidth s rem A
local notation "supply" => shrinkIssuedWords T s D rem hD small A
variable {W K : ℕ} (cur : Word W) (m : Memory W) (c : Cursor)
local notation "entry" => allocate K c (NavigationDirectory.Stage.shrink x)
local notation "p" => pointers K c x
local notation "C" => outgoing S N tagCount p
local notation "mid" => Prod.snd (Execution.run (shrinkChoices cur T) (Prod.snd (Execution.run (shrinkOld cur s D) m)))
local notation "commit" => Prod.snd (Execution.run (shrinkCostScans T cur K) mid)
local notation "code" => shrinkPublish cur K s D T

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
structure ShrinkOutput (branch : Fin (shrinkBinary T s D rem hD small A).rules.count) (out : Memory W) : Prop where
  pointer : (out cur.val).val=(entry).next.header
  stored : SlotImage.Stored ((M).next branch).graph ((M).next branch).order (tagOrdinal rem) C (fun i=>(out i).val) ((M).next branch).width
  graphInput : Input S P (B).order hc (ShrinkMotif.chooseWidths (supply branch)) p cur prior (supply branch) commit
  header : ∀ i,i≤63 → (out (c.header+i)).val=DescriptorSpan.fields K c x (ShrinkMotif.chooseWidths (supply branch)) i
  archive : ∀i,i≠cur.val → i≠c.header+27 → (i<c.heap ∨ (entry).next.heap≤ i) → out i=m i
  records : DescriptorSpan.PublishedDescriptors S K c x (ShrinkMotif.chooseWidths (supply branch)) cur 1
    (((afterRecipe S).install cur).execute cur (fun _=>0) commit).2 out
  saved : ∀ i,i<(entry).next.heap → out i=(((NodeRecipe.after S K 1).install cur).execute cur (fun _=>0) commit).2 i
  priorFrame : ∀ a,(∀ address, Read x p address a) → out a=commit a
  reopen : ∀ kernel : Word W,(out kernel.val).val=(p).ownHeader →
    Input S P (B).order hc (ShrinkMotif.chooseWidths (supply branch)) p kernel prior (supply branch) out
  keysRead : ∀ u : ((B).Base × BitWord tagCount) × Fin (liveDegree S+stagePad),
    out ((p).keys+SlotImage.ordinal (Template.tagNumber (t:=tagCount) (B).order) u)=
      (Template.sourceKey S P (B).order (shrinkPieceBound s D) (ShrinkMotif.chooseWidths (supply branch)) hc u : Word W)
  tagPos : 0<tagCount
  nativeGraph : SlotImage.Stored (successor (pad:=stagePad) S P (B).order (shrinkPieceBound s D)
      (ShrinkMotif.chooseWidths (supply branch)) hc good tagPos) (Template.tagNumber (t:=tagCount) (B).order)
      (tagOrdinal rem) C (fun i=>(out i).val)
      (newWidth (pad:=stagePad) S P (B).order (shrinkPieceBound s D) (ShrinkMotif.chooseWidths (supply branch)) hc good (supply branch))
  descGraph : SlotImage.Stored (successor (pad:=stagePad) S P (B).order (shrinkPieceBound s D)
      (ShrinkMotif.chooseWidths (supply branch)) hc good tagPos) (Template.tagNumber (t:=tagCount) (B).order)
      (tagOrdinal rem) C (fun i=>((((afterRecipe S).install cur).execute cur (fun _=>0) commit).2 i).val)
      (newWidth (pad:=stagePad) S P (B).order (shrinkPieceBound s D) (ShrinkMotif.chooseWidths (supply branch)) hc good (supply branch))
  descHeader : RAM.HeaderScan.Scans.Header cur
    (((afterRecipe S).install cur).execute cur (fun _=>0) commit).2 c.header 63
    (DescriptorSpan.fields K c x (ShrinkMotif.chooseWidths (supply branch)))
  descInput : Input S P (B).order hc (ShrinkMotif.chooseWidths (supply branch)) p cur prior (supply branch)
    (((afterRecipe S).install cur).execute cur (fun _=>0) commit).2
  cursor : CursorSpace cur m c K x
  choiceCopies : ∀ a : (P).Motif,
    (((((afterRecipe S).install cur).execute cur (fun _=>0) commit).2
      (c.heap+3*(shrinkRecordOrder s rem A a).val))).val=shrinkRecordCopies T s rem A a
  demandWords : ∀ q : (P).Motif,∀ e : Fin 2,
    (out ((p).demands+(shrinkRecordOrder s rem A q).val*2+e.val)).val=
      PhysicalShrink.b P prior (shrinkRecordCode s rem A) hc q e

  choiceShape : ∀ a : (P).Motif,
    (((((afterRecipe S).install cur).execute cur (fun _=>0) commit).2
      (c.heap+3*(shrinkRecordOrder s rem A a).val+1))).val=
      (RefreshDemandRows.tileNumber (PhysicalShrink.b P prior (shrinkRecordCode s rem A) hc a) (T.base ∘ T.row)).val
  histogramWord : ∀ (i : Fin (Q).motifs) (v : (Q).alphabet i),
    c.dense+i.val*K+(Fintype.equivFin _ v).val≠c.header+27 →
    (out (c.dense+i.val*K+(Fintype.equivFin _ v).val)).val=(((Q).order branch i).val v).val

  registerFit : (Q).Fits K W

/-- The selected history dispatcher reads the source degree from the genuine
persistent stage header, after the elected layout has been written. -/
theorem ShrinkOutput.degreeWord {branch : Fin (M).rules.count} {out : Memory W}
    (z : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out) :
    (out (c.header+48)).val=2^s := by
  have h:=z.header 48 (by decide)
  simpa only [DescriptorSpan.fields,show (48:ℕ)≠27 by decide,ite_false,
    NavigationDirectory.family_degree,Resident.dims,shrinkStage] using h


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
