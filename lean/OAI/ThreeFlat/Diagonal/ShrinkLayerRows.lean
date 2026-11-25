import OAI.ThreeFlat.Diagonal.ShrinkArchiveLayer
import OAI.ThreeFlat.Diagonal.ShrinkPublishedIncidents
import OAI.ThreeFlat.Diagonal.ShrinkPublishedHalves
import OAI.ThreeFlat.Diagonal.PhysicalShrinkBase
import OAI.ThreeFlat.Diagonal.PhysicalShrinkIncidentReads
import OAI.ThreeFlat.Diagonal.ShrinkRecordBase
import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows
import OAI.ThreeFlat.Diagonal.PhysicalIncidentWidth
import OAI.ThreeFlat.Diagonal.NavigationArchiveFields
import OAI.ThreeFlat.Diagonal.NavigationStageBounds
import OAI.ThreeFlat.Diagonal.CompressorHalfPorts
import OAI.ThreeFlat.RAM.NavigationNodeRows

namespace OAI
/-! # Native shrink descriptor reads, widths and kernel multiplicities -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.ShrinkStage.DescriptorSpan Native.Placement Native.Graph
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav NavigationNodeRows
open scoped Classical BigOperators Fin.NatCast
noncomputable section
open private palette_two from OAI.ThreeFlat.Diagonal.PhysicalShrinkPrefix
set_option quotPrecheck false
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "N" => Fintype.card (B).Base
local notation "P" => shrinkRecordPacking s rem A
local notation "d" => (2^s:ℕ)
local notation "k" => (2*d+1:ℕ)
local notation "hc" => palette_two s
local notation "S" => shrinkStage s D
local notation "t" => tagBits d
local notation "x" => dims S N t rem
local notation "prior" => shrinkRecordWidth s rem A
local notation "supply" => shrinkIssuedWords T s D rem hD small A
variable {W K : ℕ} (cur : Word W) (m : Memory W) (c : Cursor) (branch : Fin (shrinkBinary T s D rem hD small A).rules.count)
local notation "en" => allocate K c (.shrink x)
local notation "lay" => ShrinkMotif.chooseWidths (supply branch)
local notation "layer" => nodeLayer K c (.shrink x)
local notation "f" => DescriptorSpan.fields K c x lay
local notation "packSite" => Computability.VPVNP.Compression.Site (B).Base (BitWord t) (BitWord rem)

local notation "ctrl" => pointers K c x
local notation "mid" => ((shrinkChoices cur T).run ((shrinkOld cur s D).run m).2).2
local notation "commit" => ((shrinkCostScans T cur K).run mid).2
local notation "oldDesc" => (((afterRecipe S).install cur).execute cur (fun _=>0) commit).2
local notation "Dsc" => Incidents.descriptor («S» := shrinkStage s D) P (B).order Template.ptr (fun _=>cur) oldDesc (fun _=>0) hc K lay
local notation "cap" => Incidents.capacity S
local notation "z" => shrinkPackOrder s D rem A
local notation "y" => shrinkNextOrder T s D rem hD small A branch
local notation "X" => (M).next branch

private theorem halfWidthAt {size : ℕ} (width : Fin size → ℕ)
    (index : Fin (List.ofFn width).length) (slot : Fin size) (same : slot.val=index.val) :
    (List.ofFn width)[index.val]'index.isLt = width slot :=
  (List.getElem_ofFn («f» := width) index.isLt).trans (congrArg width (Fin.ext same.symm))

private theorem shrinkRowsBelow {node : Layer} (rows : LayerData node) (tape : ℕ → ℕ)
    (limit degree capacity widthBase copyBase : ℕ)
    (children : node.children + node.count * node.childCount ≤ limit)
    (headers : node.incident + 2 * node.count ≤ limit)
    (widths : widthBase + (8*degree)*node.count ≤ limit)
    (kernels : node.kernels + 5 * node.count ≤ limit)
    (copies : copyBase + (6*capacity)*node.count ≤ limit)
    (widthRead : ∀ j : Fin node.count,
      tape (node.incident+j.val*2+1) = widthBase+j.val*(8*degree))
    (copyRead : ∀ j : Fin node.count,
      tape (node.kernels+j.val*5+4) = copyBase+j.val*(6*capacity))
    (halfCount : ∀ j, (rows.halfWidth j).length ≤ 2*degree)
    (motifCount : ∀ j, (rows.motifCopies j).length ≤ capacity) :
    rows.Below limit tape := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j i
    have index := half_index_lt j.isLt i.isLt
    omega
  · intro j
    have index := half_index_lt j.isLt (by decide : 1 < 2)
    omega
  · intro j i
    rw [widthRead]
    have index := half_index_lt (half_index_lt j.isLt (i.isLt.trans_le (halfCount j)))
      (by decide : 2 < 4)
    calc
      _ = widthBase + ((j.val*(2*degree)+i.val)*4+2) := by ring
      _ < widthBase + (node.count*(2*degree))*4 := Nat.add_lt_add_left index _
      _ = widthBase + (8*degree)*node.count := by ring
      _ ≤ _ := widths
  · intro _ j
    have index := half_index_lt j.isLt (by decide : 4 < 5)
    omega
  · intro _ j i
    rw [copyRead]
    have index := half_index_lt (half_index_lt j.isLt (i.isLt.trans_le (motifCount j)))
      (by decide : 3 < 6)
    calc
      _ = copyBase + ((j.val*capacity+i.val)*6+3) := by ring
      _ < copyBase + (node.count*capacity)*6 := Nat.add_lt_add_left index _
      _ = copyBase + (6*capacity)*node.count := by ring
      _ ≤ _ := copies

private theorem shrinkAllocationBounds (alphabet : ℕ) (cursor : Cursor) (shape : Dimensions) (elected : Bool) :
    let values := DescriptorSpan.fields alphabet cursor shape elected
    let allocated := allocate alphabet cursor (.shrink shape)
    let rows := nodeLayer alphabet cursor (.shrink shape)
    values 34 = rows.kernels ∧ values 38 = rows.incident ∧ values 42 = rows.children ∧
    values 34+5*shape.outputSites ≤ allocated.next.heap ∧
    values 36+(6*shape.localCapacity)*shape.outputSites ≤ allocated.next.heap ∧
    values 38+2*shape.outputSites ≤ allocated.next.heap ∧
    values 40+(8*shape.newDegree)*shape.outputSites ≤ allocated.next.heap ∧
    values 42+shape.outputSites*(shape.oldDegree*2^shape.colorBits) ≤ allocated.next.heap := by
  have sites : shape.outputSites*(shape.oldDegree*2^shape.colorBits) = shape.originalSites := by
    unfold Dimensions.outputSites Dimensions.newBase Dimensions.originalSites Dimensions.originalLanes
    ac_rfl
  dsimp only
  rw [sites]
  simp [nodeLayer,DescriptorSpan.fields,allocate,headerExtra,extraEnd]; omega

/-- The same source and destination pointers occur in the native and mathematical
layer descriptions. All six descriptor spans end before the successor heap. -/
theorem shrink_allocated_fields :
    f 34=(layer).kernels ∧ f 38=(layer).incident ∧ f 42=(layer).children ∧
    f 34+5*(x).outputSites≤(en).next.heap ∧ f 36+(6*cap)*(x).outputSites≤(en).next.heap ∧
    f 38+2*(x).outputSites≤(en).next.heap ∧ f 40+(8*D)*(x).outputSites≤(en).next.heap ∧
    f 42+(x).outputSites*(d*2^k)≤(en).next.heap :=
  shrinkAllocationBounds K c x lay

open private rawConditions from OAI.ThreeFlat.Diagonal.PhysicalShrinkSuccessor

private theorem half_base_lower (alphabet : ℕ) (cursor : Cursor) (shape : Dimensions) (layout : Bool) :
    cursor.heap ≤ DescriptorSpan.fields alphabet cursor shape layout 38 ∧
      cursor.heap ≤ DescriptorSpan.fields alphabet cursor shape layout 40 := by
  simp [DescriptorSpan.fields,allocate,headerExtra]; omega

set_option maxHeartbeats 800000 in
/-- The row scanner also reads the uncast geometric half order of the occupied
site. Addresses are the same allocated words as those of the chronological graph. -/
theorem ShrinkOutput.selected_raw_halves {out:Memory W}
    (H:ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (df:2*D<2^W) (lf:2^rem<2^W) (v:packSite) :
    let number:=Incidents.siteNumber (B).order v
    let header:=f 38+2*number
    let base:=f 40+number*(8*D)
    let degree:=Graph.liveDegree S+PhysicalShrink.padding k d D
    let G:=Resident.successor (pad:=PhysicalShrink.padding k d D) S P (B).order (shrinkPieceBound s D) lay hc
      (rawConditions s rem (B)) H.tagPos
    let width:=Resident.newWidth (pad:=PhysicalShrink.padding k d D) S P (B).order (shrinkPieceBound s D) lay hc
      (rawConditions s rem (B)) (supply branch)
    c.heap≤header ∧ header+1<(en).next.heap ∧ c.heap≤base ∧ base+4*(2*degree)≤(en).next.heap ∧
    out header=(2*degree:ℕ) ∧ out (header+1)=((base:ℕ):Word W) ∧
    ∀j:Fin (2*degree),out (base+4*j.val+3)=
      (Halves.prefixValue G width ((v.1,v.2.1),v.2.2) j:Word W) := by
  let degree:=Graph.liveDegree S+PhysicalShrink.padding k d D
  let G:=Resident.successor (pad:=PhysicalShrink.padding k d D) S P (B).order (shrinkPieceBound s D) lay hc
    (rawConditions s rem (B)) H.tagPos
  let width:=Resident.newWidth (pad:=PhysicalShrink.padding k d D) S P (B).order (shrinkPieceBound s D) lay hc
    (rawConditions s rem (B)) (supply branch)
  let number:=Incidents.siteNumber (B).order v
  have atRow : ((z) v).val=number:=shrinkPackOrder_val s D rem A v
  have route : Halves.siteNumber (Template.tagNumber («t» := t) (B).order) ((v.1,v.2.1),v.2.2)=number:=by
    simp only [Halves.siteNumber,Template.tagNumber_val,Incidents.siteNumber,number];ring
  have deg : degree=D:=PhysicalShrink.degree_eq hc (Nat.two_pow_pos _) hD
  have nend:=((z) v).isLt
  rw [atRow] at nend
  obtain ⟨_,_,_,_,_,he,we,_⟩:=shrink_allocated_fields T s D rem hD small A (K:=K) c branch
  obtain ⟨hlo,blo⟩ := half_base_lower K c x lay
  have hEnd : f 38+2*number+1<(en).next.heap:=by omega
  have bEnd : f 40+number*(8*D)+4*(2*degree)≤(en).next.heap:=by
    have bound:=Nat.mul_le_mul_left (8*D) (Nat.succ_le_of_lt nend)
    rw [Nat.mul_succ] at bound
    rw [deg];rw [Nat.mul_comm number (8*D)]
    omega
  refine ⟨hlo.trans (Nat.le_add_right _ _),hEnd,blo.trans (Nat.le_add_right _ _),bEnd,?_,?_,?_⟩
  · have word:=PublishedDescriptors.half_header_word («S» := S) H.records H.cursor H.descHeader ((z) v) 0
    change out (f 38+2*((z) v).val) = ((2*D : ℕ) : Word W) at word
    rw [atRow] at word
    exact word.trans (congrArg (fun count : ℕ => ((2*count : ℕ) : Word W)) deg.symm)
  · have word:=PublishedDescriptors.half_header_word («S» := S) H.records H.cursor H.descHeader ((z) v) 1
    change out (f 38+(2*((z) v).val+1)) = ((f 40+((z) v).val*(8*D) : ℕ) : Word W) at word
    rw [atRow,←Nat.add_assoc] at word
    exact word
  · intro j
    have word:=PublishedDescriptors.half_prefix_of_degree («S» := S) H.records H.cursor H.descHeader G (Template.tagNumber («t» := t) (B).order) width
      H.descGraph deg rfl rfl df lf ((v.1,v.2.1),v.2.2) j (route.trans_lt nend)
    rw [route] at word
    have indexEq : f 40+number*(8*D)+4*j.val+3 =
        f 40+((number*(2*D)+j.val)*4+3) := by ring
    exact (congrArg out indexEq).trans word

/-- The actual site's five-word kernel retains the start and length of the chosen incidence list. -/
theorem ShrinkOutput.selected_kernel {out : Memory W} (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (old : ShrinkOldCaps s rem W) (baseFit : N≤2^W) (wide : 8≤W)
    (capFits : cap<2^W) (offset : 0<c.width) (site : packSite) (field : Fin 5) :
    let n:=Incidents.siteNumber (B).order site
    let occupied:=(Incidents.siteKeys («S» := shrinkStage s D) (w:=W) P (B).order lay site).length
    let word:=f 34+(5*n+field.val)
    word<(en).next.heap ∧ out word=((![c.header,n,1,occupied,f 36+n*(6*cap)] : Fin 5→ℕ) field:Word W) ∧ occupied≤cap := by
  let E:=shrinkOutputCodec s rem A old
  have slotBound : s≤W := ((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp old.slots).le
  have code (v : (B).Base) : E.base v=(((B).order v).val:Word W) := rfl
  have chart (u : BitWord s) : slotCode (w:=W) P u=tagWord slotBound u := Demand.tag_cast slotBound u
  have add (a b : BitWord s) : slotCode (w:=W) P (a+b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_add slotBound a b
  have sub (a b : BitWord s) : slotCode (w:=W) P (a-b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_sub slotBound a b

  have read:=PublishedDescriptors.kernel_words («S»:=shrinkStage s D) (kind:=1) (b:=(B).order)
    H.records H.cursor H.descHeader H.descInput E code add sub baseFit old.tags old.residual
    old.colors wide capFits offset site field
  have si : Incidents.siteNumber (B).order site<(x).outputSites :=
    DescriptorSpan.site_number_lt (b:=(B).order) site
  have column : 5*Incidents.siteNumber (B).order site+field.val<5*(x).outputSites := by
    simpa only [Nat.mul_comm 5] using DescriptorSpan.half_index_lt si field.isLt
  have stop : f 34+5*(x).outputSites≤(en).next.heap :=
    (shrink_allocated_fields T s D rem hD small A (K:=K) c branch).2.2.2.1
  obtain ⟨_,bounded,_,_⟩:=PublishedDescriptors.incident_words («S»:=shrinkStage s D) (kind:=1) (b:=(B).order)
    H.records H.cursor H.descHeader H.descInput E code add sub baseFit old.tags old.residual
    old.colors wide capFits offset site
  exact ⟨(Nat.add_lt_add_left column (f 34)).trans_le stop,read,bounded⟩

private theorem descriptor_word_below {base count capacity heap site slot field : ℕ}
    (hs : site < count) (hi : slot < capacity) (hf : field < 6)
    (bank : base + (6 * capacity) * count ≤ heap) :
    base + (6 * (capacity * site + slot) + field) < heap := by
  have index := DescriptorSpan.half_index_lt (DescriptorSpan.half_index_lt hs hi) hf
  calc
    _ = base + ((site * capacity + slot) * 6 + field) := by ac_rfl
    _ < base + (count * capacity) * 6 := Nat.add_lt_add_left index _
    _ = base + (6 * capacity) * count := by ac_rfl
    _ ≤ heap := bank

/-- Each of the six emitted words may be read using the very same enumeration retained
in the journal, including after the subsequent descriptor-bank frame. -/
theorem ShrinkOutput.selected_descriptor {out : Memory W} (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (old : ShrinkOldCaps s rem W) (baseFit : N≤2^W) (wide : 8≤W)
    (capFits : cap<2^W) (offset : 0<c.width)
    (site : packSite) (O : Incidents.SiteOrder («S» := shrinkStage s D) P (B).order lay site W)
    (slot : Fin (Incidents.siteKeys («S» := shrinkStage s D) (w:=W) P (B).order lay site).length) (field : Fin 6) :
    let addr:=f 36+(6*(cap*Incidents.siteNumber (B).order site+slot.val)+field.val)
    addr<(en).next.heap ∧ out addr=Dsc site (O.equiv slot).val field := by
  let E:=shrinkOutputCodec s rem A old
  have slotBound : s≤W := ((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp old.slots).le
  have code (v : (B).Base) : E.base v=(((B).order v).val:Word W) := rfl
  have chart (u : BitWord s) : slotCode (w:=W) P u=tagWord slotBound u := Demand.tag_cast slotBound u
  have add (a b : BitWord s) : slotCode (w:=W) P (a+b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_add slotBound a b
  have sub (a b : BitWord s) : slotCode (w:=W) P (a-b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_sub slotBound a b
  obtain ⟨q,sz,issued,_⟩ := PublishedDescriptors.incident_words («S»:=shrinkStage s D) («P»:=P)
    (b:=(B).order) (kind:=1) (raw:=m) (old:=oldDesc) (final:=out)
    H.records H.cursor H.descHeader H.descInput E code add sub baseFit old.tags old.residual
    old.colors wide capFits offset site
  have eqv:=(issued slot field)
  have same : (q.equiv slot).val=(O.equiv slot).val := by
    apply Incidents.positiveKey_inj («S»:=shrinkStage s D) (w:=W) P (B).order _ ((q.key_eq slot).symm.trans (O.key_eq slot))
    intro a
    have bound:=(Nat.add_lt_add_left (SlotImage.edgeOrdinal_lt (B).order (Demand.laneOrdinal P)
      (packedAddress.symm a)) (ctrl).oldWidths).trans_le H.descInput.widthBound
    have keyBound : (ctrl).oldWidths + Demand.key P (baseNat (B).order) a < 2^W :=
      lt_of_eq_of_lt (congrArg (fun word : ℕ => (ctrl).oldWidths + word)
        (Demand.edge_address P (B).order a).symm) bound
    change 0 < (ctrl).oldWidths at offset
    rw [Nat.add_comm _ 1]
    exact (Nat.add_le_add_right offset _).trans_lt keyBound
  rw [same] at eqv
  have si : Incidents.siteNumber (B).order site < (x).outputSites :=
    DescriptorSpan.site_number_lt (b:=(B).order) site
  have stop := (shrink_allocated_fields T s D rem hD small A (K:=K) c branch).2.2.2.2.1
  exact ⟨descriptor_word_below si (slot.isLt.trans_le sz) field.isLt stop, eqv⟩

/-- The private-width scanner may look at a descriptor after the last
occupied incidence. The issued descriptor scan filled this entire suffix with zero. -/
theorem ShrinkOutput.selected_padding {out : Memory W} (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (old : ShrinkOldCaps s rem W) (baseFit : N≤2^W) (wide : 8≤W)
    (capFits : cap<2^W) (offset : 0<c.width) (site : packSite) (i : Fin cap)
    (after : (Incidents.siteKeys («S» := shrinkStage s D) (w:=W) P (B).order lay site).length≤ i.val) (field : Fin 6) :
    let addr:=f 36+(6*(cap*Incidents.siteNumber (B).order site+i.val)+field.val)
    addr<(en).next.heap ∧ out addr=0 := by
  let E:=shrinkOutputCodec s rem A old
  have slotBound : s≤W := ((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp old.slots).le
  have code (v : (B).Base) : E.base v=(((B).order v).val:Word W) := rfl
  have chart (u : BitWord s) : slotCode (w:=W) P u=tagWord slotBound u := Demand.tag_cast slotBound u
  have add (a b : BitWord s) : slotCode (w:=W) P (a+b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_add slotBound a b
  have sub (a b : BitWord s) : slotCode (w:=W) P (a-b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_sub slotBound a b
  obtain ⟨_,_,_,zeros⟩ := PublishedDescriptors.incident_words («S»:=shrinkStage s D) («P»:=P)
    (b:=(B).order) (kind:=1) (raw:=m) (old:=oldDesc) (final:=out)
    H.records H.cursor H.descHeader H.descInput E code add sub baseFit old.tags old.residual
    old.colors wide capFits offset site
  have si : Incidents.siteNumber (B).order site < (x).outputSites :=
    DescriptorSpan.site_number_lt (b:=(B).order) site
  have stop := (shrink_allocated_fields T s D rem hD small A (K:=K) c branch).2.2.2.2.1
  exact ⟨descriptor_word_below si i.isLt field.isLt stop, zeros i.val field after i.isLt⟩

private theorem shrink_row_floors (rowK : ℕ) (cursor₀ : Cursor) (shape : Dimensions) (mode : Bool) :
    let row := DescriptorSpan.fields rowK cursor₀ shape mode
    cursor₀.heap ≤ row 34 ∧ cursor₀.heap ≤ row 36 ∧ cursor₀.heap ≤ row 38 ∧
      cursor₀.heap ≤ row 40 ∧ cursor₀.heap ≤ row 42 := by
  simp [DescriptorSpan.fields, allocate, headerExtra]; omega

private theorem bounded_layer_footprint {rowLayer : Layer} {rowData : LayerData rowLayer}
    {mem : ℕ → ℕ} {lo hi : ℕ} (below : rowData.Below hi mem)
    (childrenLo : lo ≤ rowLayer.children) (incidentLo : lo ≤ rowLayer.incident)
    (kernelsLo : lo ≤ rowLayer.kernels)
    (widthsLo : ∀ j : Fin rowLayer.count, lo ≤ mem (rowLayer.incident+j.val*2+1))
    (copiesLo : ∀ j : Fin rowLayer.count, lo ≤ mem (rowLayer.kernels+j.val*5+4)) :
    rowData.Footprint (fun i => lo ≤ i ∧ i < hi) mem := by
  have above := below.footprint
  have addOffset {a₀ : ℕ} (bound : lo ≤ a₀) (off : ℕ) : lo ≤ a₀ + off :=
    bound.trans (Nat.le_add_right _ _)
  exact ⟨fun j i => ⟨addOffset (addOffset childrenLo _) _, above.child j i⟩,
    fun j => ⟨addOffset incidentLo _, above.halves j⟩,
    fun j => ⟨addOffset (addOffset incidentLo _) _, above.halfPtr j⟩,
    fun j i => ⟨addOffset (widthsLo j) _, above.width j i⟩,
    fun nz j => ⟨addOffset (addOffset kernelsLo _) _, above.motifs nz j⟩,
    fun nz j => ⟨addOffset (addOffset kernelsLo _) _, above.motifPtr nz j⟩,
    fun nz j i => ⟨addOffset (copiesLo j) _, above.copies nz j i⟩⟩

set_option maxRecDepth 14000 in
set_option maxHeartbeats 1800000 in
/-- On the actual shrink output, simultaneous choice of the compact local site order
identifies both paid motif headers and all the words used by the charge scanner. -/
theorem ShrinkOutput.layer_records {out : Memory W} (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (old : ShrinkOldCaps s rem W) (baseFit : N≤2^W) (wide : 8≤W) (childFit : d*2^k<2^W)
    (capFits : cap<2^W) (degreeFits : 2*D<2^W) (offset : 0<c.width) (nodes : (en).next.node≤2^W) :
    ∃ O : ∀v:packSite,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order lay v W,
      let data := shrinkLayerData T s D rem hD small A (K:=K) c branch O
      data.Reads (fun i=>(out i).val) ∧ data.Below (en).next.heap (fun i=>(out i).val) ∧
      data.Footprint (fun i=>c.heap≤ i ∧ i<(en).next.heap) (fun i=>(out i).val) ∧
      (∀ j,(data.halfWidth j).length≤ stageHalves (.shrink x)) ∧
      (∀ j,(data.motifCopies j).length≤ stageMotifs (.shrink x)) := by
  have copies (site : packSite) (a : (P).Motif) : (Dsc site a 3).val=shrinkRecordCopies T s rem A a :=
    ShrinkOutput.incident_record_copies T s D rem hD small A cur m c branch H site a
  let E:=shrinkOutputCodec s rem A old
  have slotBound : s≤W := ((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp old.slots).le
  have code (v : (B).Base) : E.base v=(((B).order v).val:Word W) := rfl
  have chart (u : BitWord s) : slotCode (w:=W) P u=tagWord slotBound u := Demand.tag_cast slotBound u
  have add (a b : BitWord s) : slotCode (w:=W) P (a+b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_add slotBound a b
  have sub (a b : BitWord s) : slotCode (w:=W) P (a-b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_sub slotBound a b
  have words (v : packSite) := PublishedDescriptors.incident_words («S» := S) («P» := P) (b := (B).order) (raw := m) (old := oldDesc) (final := out) (kind := 1) H.records H.cursor H.descHeader H.descInput E code add sub
    baseFit old.tags old.residual old.colors wide capFits offset v
  choose O sized live idle using words
  let data := shrinkLayerData T s D rem hD small A (K:=K) c branch O
  refine ⟨O,?_⟩
  change data.Reads _ ∧ data.Below _ _ ∧ data.Footprint _ _ ∧ _ ∧ _
  have kernel (v : packSite) (j : Fin 5) := PublishedDescriptors.kernel_words («S» := S) («P» := P) (b := (B).order) (raw := m) (old := oldDesc) (final := out) (kind := 1) H.records H.cursor H.descHeader H.descInput
    E code add sub baseFit old.tags old.residual old.colors wide capFits offset v j
  have child (v : packSite) (j : Fin (d*2^k)) :=
    PublishedDescriptors.child_word (S₀:=S) (q:=2*d) («P» := P) (b := (B).order) (raw := m) (old := oldDesc) (final := out) (kind := 1) H.records H.cursor H.descHeader H.descInput E code add sub
      old.slots childFit ((Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2*d≤k)).trans_lt old.colors) v j
  have graph:=shrink_stored_at T s D rem hD small A branch (shrinkPieceBound s D) H.tagPos _ _ H.descGraph
  have half (j : Fin (x).outputSites) (i : Fin (2*D)) :=
    PublishedDescriptors.half_word («S» := S) H.records H.cursor H.descHeader (X).graph (X).order (X).width graph rfl rfl degreeFits old.residual
      ((y).symm j) i 2 (by rw [←shrinkNextOrder_val,(y).apply_symm_apply];exact j.isLt)
  obtain ⟨kf,hf,cf,ke,ie,he,we,ce⟩:=shrink_allocated_fields T s D rem hD small A (K:=K) c branch
  have bound : (en).next.heap<2^W := H.cursor.controls.trans_lt cur.isLt
  have sz (j : Fin (x).outputSites) : Incidents.siteNumber (B).order ((z).symm j)=j.val := by
    rw [←shrinkPackOrder_val,(z).apply_symm_apply]
  have hx (j : Fin (x).outputSites) : Halves.siteNumber (X).order ((y).symm j)=j.val := by
    rw [←shrinkNextOrder_val,(y).apply_symm_apply]
  have widthLen (j : Fin (x).outputSites) : (data.halfWidth j).length=2*D := List.length_ofFn
  have countLen (j : Fin (x).outputSites) : (data.motifCopies j).length=
      (Incidents.siteKeys («S» := shrinkStage s D) (w:=W) P (B).order lay ((z).symm j)).length := List.length_ofFn
  have hp (j : Fin (x).outputSites) : (out ((layer).incident+j.val*2+1)).val=f 40+j.val*(8*D) := by
    have word:=PublishedDescriptors.half_header_word («S» := S) H.records H.cursor H.descHeader j 1
    change out (f 38+(2*j.val+1))=((f 40+j.val*(8*D):ℕ):Word W) at word
    have less:=Nat.mul_le_mul_right (8*D) j.isLt
    rw [Nat.succ_mul] at less
    have fit : f 40+j.val*(8*D)<2^W := by rw [Nat.mul_comm (8*D) (x).outputSites] at we;omega
    rw [←hf,show f 38+j.val*2+1=f 38+(2*j.val+1) by ring,word,Fin.val_cast_of_lt fit]
  have mp (j : Fin (x).outputSites) : (out ((layer).kernels+j.val*5+4)).val=f 36+j.val*(6*cap) := by
    have word:=kernel ((z).symm j) 4
    rw [sz] at word
    change out (f 34+(5*j.val+4))=((f 36+j.val*(6*cap):ℕ):Word W) at word
    have less:=Nat.mul_le_mul_right (6*cap) j.isLt
    rw [Nat.succ_mul] at less
    have cp : 0<cap := by change 0<8*d^2*2^k;positivity
    have fit : f 36+j.val*(6*cap)<2^W := by rw [Nat.mul_comm (6*cap) (x).outputSites] at ie;omega
    rw [←kf,show f 34+j.val*5+4=f 34+(5*j.val+4) by ring,word,Fin.val_cast_of_lt fit]
  have known : data.Reads (fun i=>(out i).val) ∧ data.Below (en).next.heap (fun i=>(out i).val) := by
    refine ⟨⟨?_,?_,?_,?_,?_⟩,?_⟩
    · intro j i
      let site := (z).symm j
      let position := (Owner.childOrder P lay site i).val
      have word : out (f 42+(Incidents.siteNumber (B).order site*(d*2^k)+i.val)) =
          ((c.node+ChildRows.oldNumber P (B).order position : ℕ) : Word W) := child site i
      have index : Incidents.siteNumber (B).order site = j.val := sz j
      have address : (layer).children+j.val*(layer).childCount+i.val =
          f 42+(Incidents.siteNumber (B).order site*(d*2^k)+i.val) := by
        change (layer).children+j.val*(d*2^k)+i.val=_
        rw [←cf, index, Nat.add_assoc]
      have bounded : ChildRows.oldNumber P (B).order position < (x).originalSites :=
        ChildRows.oldNumber_lt P (B).order position
      have limit : c.node+(x).originalSites ≤ 2^W := nodes
      have fit := (Nat.add_lt_add_left bounded c.node).trans_le limit
      exact ((congrArg (fun n => (out n).val) address).trans (congrArg Fin.val word)).trans
        (Fin.val_cast_of_lt fit)
    · intro j
      have word := PublishedDescriptors.half_header_word («S» := S) H.records H.cursor H.descHeader j 0
      change out (f 38+(2*j.val+0))=((2*D:ℕ):Word W) at word
      have address : (layer).incident+j.val*2 = f 38+(2*j.val+0) :=
        congrArg₂ Nat.add hf.symm ((Nat.mul_comm j.val 2).trans (Nat.add_zero (2*j.val)).symm)
      exact (((congrArg (fun n => (out n).val) address).trans (congrArg Fin.val word)).trans
        (Fin.val_cast_of_lt degreeFits)).trans (widthLen j).symm
    · intro j i
      let a : Fin (2*D):=⟨i.val,by rw [←widthLen j];exact i.isLt⟩
      let e:=Halves.sourceHalf (X).graph ((y).symm j) a
      have word := half j a
      change out (f 40+((Halves.siteNumber (X).order ((y).symm j)*(2*D)+a.val)*4+2)) =
        ((X).width e : Word W) at word
      rw [hx j] at word
      have address : (out ((layer).incident+j.val*2+1)).val+(4*i.val+2) =
          f 40+((j.val*(2*D)+a.val)*4+2) := by
        rw [hp j]
        dsimp only [a]
        ring
      have fit : (X).width e < 2^W := (H.stored.widthWord e).symm.trans_lt (Fin.isLt _)
      have width : (data.halfWidth j)[i] = (X).width e :=
        halfWidthAt
          (width := fun slot : Fin (2*D) => (X).width (Halves.sourceHalf (X).graph ((y).symm j) slot))
          (index := i) (slot := a) rfl
      exact (congrArg (fun address => (out address).val) address).trans
        ((congrArg Fin.val word).trans ((Fin.val_cast_of_lt fit).trans width.symm))
    · intro _ j
      let site := (z).symm j
      let length := (Incidents.siteKeys («S» := shrinkStage s D) (w:=W) P (B).order lay site).length
      have word : out (f 34+(5*Incidents.siteNumber (B).order site+3)) = (length : Word W) :=
        kernel site 3
      have index : Incidents.siteNumber (B).order site = j.val := sz j
      have address : (layer).kernels+j.val*5+3 = f 34+(5*Incidents.siteNumber (B).order site+3) := by
        rw [←kf, index]
        ring
      have bounded : length < 2^W := (sized site).trans_lt capFits
      exact (((congrArg (fun n => (out n).val) address).trans (congrArg Fin.val word)).trans
        (Fin.val_cast_of_lt bounded)).trans (countLen j).symm
    · intro _ j i
      let a : Fin (Incidents.siteKeys («S» := shrinkStage s D) (w:=W) P (B).order lay ((z).symm j)).length:=⟨i.val,by rw [←countLen j];exact i.isLt⟩
      let site := (z).symm j
      let motif := ((O site).equiv a).val
      have word : out (f 36+(6*(cap*Incidents.siteNumber (B).order site+a.val)+3)) =
          Dsc site motif 3 := live site a 3
      have index : Incidents.siteNumber (B).order site = j.val := sz j
      have address : (out ((layer).kernels+j.val*5+4)).val + (6*i.val+3) =
          f 36+(6*(cap*Incidents.siteNumber (B).order site+a.val)+3) := by
        rw [mp j, index]
        dsimp only [a]
        ring
      have value := ((congrArg (fun n => (out n).val) address).trans (congrArg Fin.val word)).trans
        (copies site motif)
      let multiplicity := fun slot : Fin (Incidents.siteKeys («S» := shrinkStage s D) (w:=W)
        P (B).order lay site).length => shrinkRecordCopies T s rem A ((O site).equiv slot).val
      have selected := halfWidthAt (width := multiplicity) (index := i) (slot := a) rfl
      exact value.trans selected.symm
    · exact shrinkRowsBelow data (fun a => (out a).val) (en).next.heap D cap (f 40) (f 36)
        (by rw [←cf]; exact ce) (by rw [←hf]; exact he) we (by rw [←kf]; exact ke) ie
        hp mp (fun j => (widthLen j).le) (fun j => (countLen j).le.trans (sized _))
  obtain ⟨kernelLo,motifLo,incidentLo,widthLo,childLo⟩ := shrink_row_floors K c x lay
  have footprint := bounded_layer_footprint known.2 (childLo.trans_eq cf) (incidentLo.trans_eq hf)
    (kernelLo.trans_eq kf)
    (fun j => (widthLo.trans (Nat.le_add_right _ _)).trans_eq (hp j).symm)
    (fun j => (motifLo.trans (Nat.le_add_right _ _)).trans_eq (mp j).symm)
  exact ⟨known.1,known.2,footprint,fun j => (widthLen j).le,
    fun j => (countLen j).le.trans (sized ((z).symm j))⟩


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
