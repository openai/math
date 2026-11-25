import OAI.ThreeFlat.RAM.HistoryShrinkArms

namespace OAI
set_option quotPrecheck false
set_option maxErrors 600

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression Diagonal Diagonal.PhysicalStage
open Diagonal.CompressorPacking Diagonal.CompressorPacking.PhysicalShrink
open Diagonal.CompressorPacking.Native Diagonal.CompressorPacking.Native.ShrinkStage
open Diagonal.NavigationDirectory Diagonal.NavigationPass Diagonal.ShrinkStageNav
open HistoryStageBody.Physical HistoryGatherBody
open scoped Classical BigOperators Fin.CommRing
noncomputable section


open Diagonal.CompressorPacking.Native.ShrinkStage.Resident HistoryMotifJoin
/-- Geometric and directory reads on the exterior of all S17 port buffers. -/
structure PortFootprint {W : ℕ} (J : HistoryGatherBody.Layout) (input : Memory W)
    (x : Diagonal.CompressorPacking.Native.ShrinkStage.Dimensions) (p : Diagonal.CompressorPacking.Native.ShrinkStage.Pointers) : Prop where
  cursor : let a:=((J.nodePorts.cursor:Word W)).val
    a<J.temp ∨ HistoryGatherExecution.portsEnd J≤a
  node : let a:=(nodeWord J input+5).val
    a<J.temp ∨ HistoryGatherExecution.portsEnd J≤a
  kernel : let a:=((selected J input).kernel+4).val
    a<J.temp ∨ HistoryGatherExecution.portsEnd J≤a
  choice : let a:=((selected J input).incident+2).val
    a<J.temp ∨ HistoryGatherExecution.portsEnd J≤a
  key : let a:=(selected J input).incident.val
    a<J.temp ∨ HistoryGatherExecution.portsEnd J≤a
  stage : let a:=(selected J input).kernel.val
    a<J.temp ∨ HistoryGatherExecution.portsEnd J≤a
  data : ∀a,Resident.GeometryRead x p a→a<J.temp ∨ HistoryGatherExecution.portsEnd J≤a
  port : ∀(side : Bool) (i : ℕ),i<HistoryGatherExecution.cap J side →
    let a:=((selected J input).portPage+((if side then HistoryPortCatalogue.supplyBase J.demandCap+i
      else HistoryPortCatalogue.demandBase+2*i:ℕ):Word W)).val
    a<J.temp ∨ HistoryGatherExecution.portsEnd J≤a

theorem PortFootprint.after_port {W : ℕ} {J : HistoryGatherBody.Layout} {input old scratch : Memory W}
    {x : Diagonal.CompressorPacking.Native.ShrinkStage.Dimensions} {p : Diagonal.CompressorPacking.Native.ShrinkStage.Pointers}
    (foot : PortFootprint J input x p) (prior : Resident.GeometryFrame x p old input)
    (frame : DescriptorScan.agreesOutside J.temp (HistoryGatherExecution.portsEnd J) scratch input)
    (side : Bool) (i : ℕ) (valid : i<HistoryGatherExecution.cap J side) :
    Resident.GeometryFrame x p old scratch ∧
      scratch (selected J scratch).kernel.val=input (selected J input).kernel.val ∧
      scratch (selected J scratch).incident.val=input (selected J input).incident.val ∧
      portCode J scratch side i=portCode J input side i := by
  have ctr:=frame _ foot.cursor
  have node:=frame _ foot.node
  have kernel : (selected J scratch).kernel=(selected J input).kernel:=by
    change scratch (nodeWord J scratch+5).val=_
    rw [node_stable J ctr,node];rfl
  have rows:=selected_rows_same J ctr node (frame _ foot.kernel) (frame _ foot.choice)
  refine ⟨fun a ha=>(frame a (foot.data a ha)).trans (prior a ha),?_,?_,?_⟩
  · rw [kernel];exact frame _ foot.stage
  · rw [rows.1];exact frame _ foot.key
  · unfold portCode wordAt
    rw [rows.2.2]
    exact frame _ (foot.port side i valid)

section PublishedParty
open private colors_le from OAI.ThreeFlat.Diagonal.PhysicalShrinkFamily
variable {F : Type} [Field F] [Fintype F] (B : Block F) (s D rem : ℕ) (hD : 0<D)
  (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "T₀" => B.shrink
local notation "M₀" => shrinkBinary T₀ s D rem hD small A
local notation "B₀" => shrinkRecordState s rem A
local notation "N₀" => Fintype.card (B₀).Base
local notation "P₀" => shrinkRecordPacking s rem A
local notation "d₀" => (2^s:ℕ)
local notation "hc₀" => colors_le s
local notation "S₀" => shrinkStage s D
local notation "t₀" => Diagonal.CompressorPacking.tagBits d₀
local notation "x₀" => dims S₀ N₀ t₀ rem
variable {W K : ℕ} (cur ctr : Word W) (before issued final post : Memory W) (c : Cursor) (branch : Fin (shrinkBinary B.shrink s D rem hD small A).rules.count)
local notation "issuedWords" => shrinkIssuedWords T₀ s D rem hD small A branch
local notation "lay₀" => ShrinkMotif.chooseWidths issuedWords
local notation "en₀" => allocate K c (.shrink x₀)
local notation "f₀" => DescriptorSpan.fields K c x₀ lay₀
variable (hdr : ℕ) (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (saved : let x := Resident.dims (shrinkStage s D) (Fintype.card (shrinkRecordState s rem A).Base)
                         (Diagonal.CompressorPacking.tagBits (2^s)) rem
             let next := (allocate K c (.shrink x)).next
             SavedFrame cur ctr hdr next.header next.heap issued final)
    (site : Computability.VPVNP.Compression.Site (shrinkRecordState s rem A).Base
      (BitWord (Diagonal.CompressorPacking.tagBits (2^s))) (BitWord rem))
    (O : Incidents.SiteOrder (S:=shrinkStage s D) (shrinkRecordPacking s rem A)
      (shrinkRecordState s rem A).order
      (ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)) site W)
    (slot : Fin (Incidents.siteKeys (S:=shrinkStage s D) (w:=W) (shrinkRecordPacking s rem A) (shrinkRecordState s rem A).order
      (ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)) site).length)
local notation "m₀" => (O.equiv slot).val
local notation "prior" => shrinkRecordWidth s rem A
local notation "du" => PhysicalShrink.b P₀ prior (shrinkRecordCode s rem A) hc₀
local notation "bestIndex" => RefreshDemandRows.tileNumber (du m₀) ((T₀).base ∘ (T₀).row)
local notation "ordinal" => (shrinkRecordOrder s rem A m₀).val
local notation "baseRow" => f₀ 36+6*(Incidents.capacity S₀*Incidents.siteNumber (B₀).order site+slot.val)
private abbrev publishedIncidentRow (K : ℕ) (c : Cursor) (s D rem : ℕ)
    (A : State (2^s) (shrinkCharge s+rem)) (widths : Bool)
    (site : Computability.VPVNP.Compression.Site (shrinkRecordState s rem A).Base
      (BitWord (Diagonal.CompressorPacking.tagBits (2^s))) (BitWord rem)) (slotId : ℕ) : ℕ :=
  let x := Resident.dims (shrinkStage s D) (Fintype.card (shrinkRecordState s rem A).Base)
    (Diagonal.CompressorPacking.tagBits (2^s)) rem
  DescriptorSpan.fields K c x widths 36 + 6*(Incidents.capacity (shrinkStage s D)*
    Incidents.siteNumber (shrinkRecordState s rem A).order site + slotId)

variable (J : HistoryGatherBody.Layout)
    (oldCaps : ShrinkOldCaps s rem W) (baseFit : Fintype.card (shrinkRecordState s rem A).Base≤2^W) (wide : 8≤W)
    (capFits : Incidents.capacity (shrinkStage s D)<2^W) (offset : 0<c.width)
    (rowPtr : let widths := ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)
              (selected J post).incident=(publishedIncidentRow K c s D rem A widths site slot.val : Word W))
    (apart : let widths := ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)
             let row := publishedIncidentRow K c s D rem A widths site slot.val
             ∀j:Fin 6,row+j.val≠cur.val ∧ row+j.val≠ctr.val ∧ hdr≤row+j.val)
    (preserved : let widths := ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)
                 let row := publishedIncidentRow K c s D rem A widths site slot.val
                 ∀j:Fin 6,post (row+j.val)=final (row+j.val))

local notation "siteNo" => Incidents.siteNumber (B₀).order site
local notation "kernelBase" => f₀ 34+5*siteNo

include H saved oldCaps baseFit wide capFits offset in
omit [Fintype F] in
/-- A selected node's directory pointer suffices to reopen its kernel, exact incidence row
and branch mask scanner in both the bounded gather and the natural-number batch header. -/
theorem recorded_kernel
    (nodePtr : (selected J post).kernel=(kernelBase:Word W)) (atSlot : J.party.motif=slot.val)
    (guard : ∀j:Fin 5,kernelBase+j.val≠cur.val ∧ kernelBase+j.val≠ctr.val ∧ hdr≤kernelBase+j.val)
    (kept : ∀j:Fin 5,post (kernelBase+j.val)=final (kernelBase+j.val)) :
    (selected J post).incident=(publishedIncidentRow K c s D rem A lay₀ site slot.val : Word W) ∧
    (wordAt post (selected J post).kernel 3).val=(Incidents.siteKeys (S:=shrinkStage s D) (w:=W) P₀ (B₀).order lay₀ site).length ∧
    (post (selected J post).kernel.val).val=(pointers K c x₀).ownHeader := by
  let count:=(Incidents.siteKeys (S:=shrinkStage s D) (w:=W) P₀ (B₀).order lay₀ site).length
  have ptr : (selected J post).kernel=((kernelBase : ℕ) : Word W) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using nodePtr
  have kernel (j:Fin 5) : wordAt post (selected J post).kernel j.val=
      ((![c.header,siteNo,1,count,f₀ 36+siteNo*(6*Incidents.capacity S₀)] : Fin 5→ℕ) j:Word W) := by
    have data:=ShrinkOutput.selected_kernel T₀ s D rem hD small A cur before c branch H oldCaps baseFit wide
      capFits offset site j
    have address : kernelBase+j.val = f₀ 34+(5*siteNo+j.val) := Nat.add_assoc _ _ _
    have below : kernelBase+j.val < (en₀).next.heap := address.trans_lt data.1
    have fits : kernelBase+j.val < 2^W :=
      lt_trans (lt_of_lt_of_le below H.cursor.controls) cur.isLt
    have room:=guard j
    unfold wordAt
    rw [ptr,←Nat.cast_add,Fin.val_cast_of_lt fits,kept j,
      saved _ room.1 room.2.1 (.inr room.2.2) below]
    exact (congrArg issued address).trans data.2.1
  have countFit : count<2^W := by
    have cert:=ShrinkOutput.selected_kernel T₀ s D rem hD small A cur before c branch H oldCaps baseFit wide capFits offset site 0
    exact cert.2.2.trans_lt capFits
  refine ⟨?_,?_,?_⟩
  · change wordAt post (selected J post).kernel 4+(6*J.party.motif:ℕ)=((baseRow : ℕ) : Word W)
    rw [show wordAt post (selected J post).kernel 4=((f₀ 36+siteNo*(6*Incidents.capacity S₀):ℕ):Word W) from kernel 4,atSlot,
      ←Nat.cast_add]
    apply congrArg (fun k : ℕ => (k : Word W))
    ring
  · change (wordAt post (selected J post).kernel 3).val=count
    rw [show wordAt post (selected J post).kernel 3=(count:Word W) from kernel 3,Fin.val_cast_of_lt countFit]
  · have h : wordAt post (selected J post).kernel 0=(c.header:Word W):=kernel 0
    have fit:=H.cursor.header.fit
    change (post (selected J post).kernel.val).val=c.header
    simpa only [wordAt,Nat.cast_zero,add_zero,Fin.val_cast_of_lt (show c.header<2^W by omega)] using congrArg Fin.val h

local notation "descMid" => ((shrinkChoices cur T₀).run ((shrinkOld cur s D).run before).2).2
local notation "descCommit" => ((shrinkCostScans T₀ cur K).run descMid).2
local notation "descOld" => (((afterRecipe S₀).install cur).execute cur (fun _=>0) descCommit).2
local notation "descriptorWord" => Incidents.descriptor (S:=shrinkStage s D) P₀ (B₀).order Template.ptr (fun _=>cur) descOld (fun _=>0) hc₀ K lay₀ site m₀
include H saved oldCaps baseFit wide capFits offset rowPtr apart preserved in
omit [Fintype F] in
theorem recorded_word (j : Fin 6) : wordAt post (selected J post).incident j.val=descriptorWord j := by
  have row:=ShrinkOutput.selected_descriptor T₀ s D rem hD small A cur before c branch H oldCaps baseFit wide capFits offset site O slot j
  rw [←Nat.add_assoc] at row
  have r:=(apart j)
  unfold wordAt
  rw [rowPtr,←Nat.cast_add,Fin.val_cast_of_lt (lt_trans (lt_of_lt_of_le row.1 H.cursor.controls) cur.isLt),preserved j,
    saved _ r.1 r.2.1 (.inr r.2.2) row.1]
  exact row.2


private abbrev recordedRoleCount (mask : Fin 6 → Prop) := Fintype.card {j // mask j}

private theorem recordedBit {p : Prop} {d : Decidable p} {bit : Bool}
    (h : bit = @decide p d) : bit = @decide p (Classical.propDecidable p) :=
  h.trans (congrArg (fun decision : Decidable p => @decide p decision) (Subsingleton.elim _ _))

set_option maxHeartbeats 1200000 in
include H saved oldCaps baseFit wide capFits offset rowPtr apart preserved in
omit [Fintype F] in
/-- Real six-word site selected on this branch. A journal frame and the party cursor
select the actual published row for this occurrence rather than another copy of its key. -/
theorem recorded_fields (party : Fin 6) :
    let incidentWords:=wordAt post (selected J post).incident
    (incidentWords 1).val=c.dense+ordinal*K ∧ (incidentWords 2).val=(bestIndex).val ∧
    (incidentWords 3).val=shrinkRecordCopies T₀ s rem A m₀ ∧
    (incidentWords 5).val.testBit party.val =
      @decide (partySite P₀ lay₀ m₀ party=site) (Classical.propDecidable _) := by
  have words (j : Fin 6) := recorded_word B s D rem hD small A cur ctr before issued final post c branch hdr H saved
    site O slot J oldCaps baseFit wide capFits offset rowPtr apart preserved j
  refine ⟨(congrArg Fin.val (words 1)).trans ?_, (congrArg Fin.val (words 2)).trans ?_,
    (congrArg Fin.val (words 3)).trans ?_,
    (congrArg (fun x : Word W => x.val.testBit party.val) (words 5)).trans ?_⟩
  · exact ShrinkOutput.incident_record_histogram T₀ s D rem hD small A cur before c branch H site m₀
  · exact ShrinkOutput.incident_record_tile T₀ s D rem hD small A cur before c branch H site m₀
  · exact ShrinkOutput.incident_record_copies T₀ s D rem hD small A cur before c branch H site m₀
  · exact recordedBit (Incidents.party_bit (S:=shrinkStage s D) P₀ (B₀).order Template.ptr
      (fun _=>cur) descOld (fun _=>0) hc₀ K lay₀ site m₀ (by omega) party)

include H saved oldCaps baseFit wide capFits offset apart preserved in
omit [Fintype F] in
/-- Both numerical fields needed by the motif chart are read from the genuine
six-word descriptor and its selected five-word kernel. -/
theorem recorded_party_order (nodePtr : (selected J post).kernel=(kernelBase:Word W))
    (atSlot : J.party.motif=slot.val) (six : J.party.parties=6)
    (guard : ∀j:Fin 5,kernelBase+j.val≠cur.val ∧ kernelBase+j.val≠ctr.val ∧ hdr≤kernelBase+j.val)
    (kept : ∀j:Fin 5,post (kernelBase+j.val)=final (kernelBase+j.val)) :
    Fintype.card {j : Fin J.party.parties //selectedBit J post j.val}=
      recordedRoleCount (fun j => partySite P₀ lay₀ m₀ j=site) ∧
    ∀ i : Fin (recordedRoleCount (fun j => partySite P₀ lay₀ m₀ j=site)),
      role J post i.val=(Diagonal.HistoryMaskOrder.order (fun j=>partySite P₀ lay₀ m₀ j=site) i).val.val := by
  have ker:=recorded_kernel B s D rem hD small A cur ctr before issued final post c branch hdr H saved
    site slot J oldCaps baseFit wide capFits offset nodePtr atSlot guard kept
  apply selected_six_roles J post six (fun j => partySite P₀ lay₀ m₀ j=site)
  · rw [atSlot,ker.2.1];exact slot.isLt
  · intro j
    exact (recorded_fields B s D rem hD small A cur ctr before issued final post c branch hdr H saved
      site O slot J oldCaps baseFit wide capFits offset ker.1 apart preserved j).2.2.2

private theorem supply_row_room {bits bins : ℕ} {control : Word bits} {mem : Memory bits}
    {cursor : Cursor} {shape : Dimensions} (space : CursorSpace control mem cursor bins shape)
    {idx : ℕ} (bound : idx < shape.motifs) :
    (pointers bins cursor shape).supply + 8*idx + 8 ≤ 2^bits := by
  obtain ⟨_, _, demand, split, colors, offsets, graph, keys, widths, _⟩ := space.allocated
  have finish := space.end_lt
  omega

private abbrev incidentOwnerWith {J G E : Type} (choice : DecidableEq G)
    (src dst : E → J) (place : J → G) (edge : E) : Option G :=
  letI : DecidableEq G := choice
  MotifKernel.wireOwner src dst place edge

private theorem recordedOwnerBit {J G E : Type} (src dst : E → J) (place : J → G)
    (edge : E) (site : G) (first second : DecidableEq G) {bit : Bool}
    {d : Decidable (incidentOwnerWith first src dst place edge = some site)}
    (h : bit = @decide (incidentOwnerWith first src dst place edge = some site) d) :
    bit = @decide (incidentOwnerWith second src dst place edge = some site) (Classical.propDecidable _) := by
  have same : first = second := Subsingleton.elim _ _
  cases same
  exact recordedBit h

section
open Computability.VPVNP.BurstRAM.PrivateRAM Diagonal.CompressorPacking.Native.ShrinkStage
private theorem recordedAbsorbedDescriptor {V H₁ : Type} [AddCommGroup H₁]
    [Fintype V] [Fintype H₁] {w t l N : ℕ} {S : Graph.Stage}
    (P : PackingData V H₁ (BitWord t) (BitWord l) S.degree S.colors)
    (b : V ≃ Fin N) (ptr : RAM.PhysicalPinsExpr.Formula 1) (data : RAM.PhysicalPinsExpr.Param → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
    (hc : 2 ≤ S.colors) (K : ℕ) (lay : Bool)
    (site : Computability.VPVNP.Compression.Site V (BitWord t) (BitWord l)) (z : P.Motif)
    (fit : 8 ≤ w) (j : Fin 8) (chosen : DecidableEq (Computability.VPVNP.Compression.Site V (BitWord t) (BitWord l))) :
    ((Incidents.descriptor P b ptr data mem vs hc K lay site z 4).val.testBit j.val) =
      @decide (incidentOwnerWith chosen supplyGraph.tail supplyGraph.head (partySite P lay z) j = some site)
        (Classical.propDecidable _) :=
  recordedOwnerBit supplyGraph.tail supplyGraph.head (partySite P lay z) j site
    (fun x y => instDecidableEqProd x y) chosen (Incidents.absorbed_owner (S:=S) P b ptr data mem vs hc K lay site z fit j)
end

section RecordedPrivate
open private selectedSiteDecidableEq from OAI.ThreeFlat.Diagonal.ShrinkSelectedSupply
attribute [local instance 2000] selectedSiteDecidableEq

set_option maxHeartbeats 1200000 in
include H saved oldCaps baseFit wide capFits offset apart preserved in
/-- Reopen the nine genuine prefix cells of the current occupied motif. The
incident mask and its eight issued widths come from one and the same stage. -/
def recorded_private (nodePtr : (selected J post).kernel=(kernelBase:Word W))
    (atSlot : J.party.motif=slot.val)
    (kguard : ∀j:Fin 5,kernelBase+j.val≠cur.val ∧ kernelBase+j.val≠ctr.val ∧ hdr≤kernelBase+j.val)
    (kkeep : ∀j:Fin 5,post (kernelBase+j.val)=final (kernelBase+j.val))
    (geo : GeometryFrame x₀ (pointers K c x₀) issued post)
    (kind : J.mode=.shrink S₀) (stride : J.histogramStride=K) (kp : 0<K) (kfit : K<2^W) :
    PrivateSite (geo:=S₀) J post
      (fun e=>MotifKernel.wireOwner supplyGraph.tail supplyGraph.head (partySite P₀ lay₀ m₀) e=some site)
      (issuedWords m₀) := by
  have actual:=recorded_kernel B s D rem hD small A cur ctr before issued final post c branch hdr H saved
    site slot J oldCaps baseFit wide capFits offset nodePtr atSlot kguard kkeep
  have recorded:=recorded_fields B s D rem hD small A cur ctr before issued final post c branch hdr H saved
    site O slot J oldCaps baseFit wide capFits offset actual.1 apart preserved 0
  let view:=H.reopenAt post geo (selected J post).kernel actual.2.2
  refine ⟨c.dense,(pointers K c x₀).supply,ordinal,kind,?_,view.hdr.native 1,?_,
    view.hdr.native 3,?_,?_,wide,stride.symm ▸ kp,stride.symm ▸ kfit,?_,?_⟩
  · rw [atSlot,actual.2.1];exact slot.isLt
  · apply Fin.ext
    rw [stride,←recorded.1]
    exact (Fin.val_cast_of_lt (wordAt post (selected J post).incident 1).isLt).symm
  · intro j
    rw [← Nat.add_assoc, Nat.mul_comm 8]
    have stored : post ((pointers K c x₀).supply + ordinal * 8 + j.val) =
        (issuedWords m₀ j : Word W) := view.issuedRows m₀ j
    exact stored
  · intro j
    have four : wordAt post (selected J post).incident 4 = descriptorWord (4 : Fin 6) :=
      recorded_word B s D rem hD small A cur ctr before issued final post c branch hdr H saved
        site O slot J oldCaps baseFit wide capFits offset actual.1 apart preserved 4
    refine (congrArg (fun word : Word W => word.val.testBit j.val) four).trans ?_
    exact recordedAbsorbedDescriptor (S:=shrinkStage s D) P₀ (B₀).order Template.ptr
      (fun _=>cur) descOld (fun _=>0) hc₀ K lay₀ site m₀ wide j selectedSiteDecidableEq
  · rw [stride,←recorded.1];exact (wordAt post (selected J post).incident 1).isLt
  · exact supply_row_room H.cursor (show ordinal < (x₀).motifs from (shrinkRecordOrder s rem A m₀).isLt)

end RecordedPrivate

end PublishedParty
end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
