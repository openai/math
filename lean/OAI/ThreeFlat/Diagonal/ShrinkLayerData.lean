import OAI.ThreeFlat.Diagonal.ShrinkNativeHalfRows
import OAI.ThreeFlat.Diagonal.ShrinkLayerRows
import OAI.ThreeFlat.Diagonal.NavigationNodeArchive
import OAI.ThreeFlat.Diagonal.ShrinkPublishedIncidents
import OAI.ThreeFlat.Diagonal.ShrinkPublishedHalves
import OAI.ThreeFlat.Diagonal.ShrinkPublishedChildren
import OAI.ThreeFlat.Diagonal.PhysicalShrinkBase
import OAI.ThreeFlat.Diagonal.PhysicalIndividualCharge

namespace OAI
/-! # The child, half and occupied-motif rows charged to each physical shrink successor -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.ShrinkStage.DescriptorSpan Native.Placement Native.Graph
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav NavigationNodeRows
open scoped Classical BigOperators Fin.NatCast
noncomputable section
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "baseSites" => Fintype.card (State.Base (shrinkRecordState s rem A))
local notation "P" => shrinkRecordPacking s rem A
local notation "d" => (2^s:ℕ)
local notation "paletteSize" => (2*d+1:ℕ)
local notation "S" => shrinkStage s D
local notation "t" => CompressorPacking.tagBits d
local notation "x" => dims S baseSites t rem
local notation "supply" => shrinkIssuedWords T s D rem hD small A
local notation "packSite" => Computability.VPVNP.Compression.Site (State.Base (shrinkRecordState s rem A)) (BitWord t) (BitWord rem)
local notation "cap" => Incidents.capacity S

open private scalar_summands from OAI.ThreeFlat.Diagonal.PhysicalShrinkWordSpace

private theorem layer_fixed_bounds {limit : ℕ} (fixed : shrinkFixedWords T s D ≤ limit) :
    d ≤ limit ∧ 2^paletteSize ≤ limit ∧ D ≤ limit ∧ shrinkWidthFactor T s ≤ limit := by
  let tags := ThreeFlat.Diagonal.tagBits d
  obtain ⟨colors,slots,_,_,degree,_,_,_,_,_,factor⟩ :=
    scalar_summands (slots:=d) (colors:=2^paletteSize) (tags:=2^tags) (bundle:=3*(2^paletteSize*d)/4)
      (degree:=D) (pieces:=(S).pieceRadix) (keys:=keyBound S 1 tags)
      (tiles:=T.more.length) (demand:=widthMultiplicity paletteSize d) (table:=shrinkBaseBound T)
      (issued:=shrinkMotifWidthFactor T paletteSize d) (v:=limit) fixed
  exact ⟨slots,colors,degree,factor⟩

include hD small in
theorem shrinkNativeCaps_at_scale {u : ℕ} (hu : 40≤u) (fixed : shrinkFixedWords T s D≤u)
    (arena : (Stage.shrink x).heapWords≤2^(u^10)) (wire : A.maxWidth+1≤(2^(u^10))^4) :
    ShrinkNativeCaps T s D rem (16*u^10) A := by
  obtain ⟨old,extra,_,demand,issued,score⟩:=shrink_scalar_room T s D rem hD small A hu fixed arena wire
  let v:=2^(u^10)
  have uv : u≤v := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_self_pow (by decide) _))
  have big : 2^(16*u^10)=v^16 := by rw [Nat.mul_comm,pow_mul]
  have ov : 1<v:=by omega
  obtain ⟨slots,colors,deg,_⟩ := layer_fixed_bounds T s D (fixed.trans uv)
  have halfCount:2*D<2^(16*u^10):=by
    rw [big]
    have base:2*v≤v^2:=by rw [pow_two];exact Nat.mul_le_mul_right v ov
    have growth:v^2<v^16:=Nat.pow_lt_pow_right ov (by decide)
    omega
  have motifOrder := Fintype.card_congr (shrinkRecordOrder s rem A)
  rw [Fintype.card_fin] at motifOrder
  refine ⟨old,⟨((Nat.le_mul_of_pos_right baseSites (Nat.two_pow_pos t)).trans extra.bases),?_⟩,extra,demand,issued,halfCount,by rw [motifOrder];exact score⟩
  rw [big]
  calc
    Incidents.capacity S=8*d^2*2^paletteSize:=rfl
    _≤v*v^2*v:=by gcongr; omega
    _=v^4:=by ring
    _<v^16:=Nat.pow_lt_pow_right ov (by decide)

/-- The row scanner fits at the diagonal word width with the same fixed-table and
chronological arena hypotheses used by the native shrink admission call. -/
theorem shrink_layer_footprint_at_scale {u K : ℕ} (hu : 40≤u) (cur : Word (16*u^10)) (m out : Memory (16*u^10))
    (c : Cursor) (branch : Fin (M).rules.count)
    (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (fixed : shrinkFixedWords T s D≤u) (arena : (Stage.shrink x).heapWords≤2^(u^10))
    (wire : A.maxWidth+1≤(2^(u^10))^4) (offset : 0<c.width)
    (ids : (allocate K c (.shrink x)).next.node≤2^(16*u^10)) :
    ∃ O : ∀v:packSite,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order (ShrinkMotif.chooseWidths (supply branch)) v (16*u^10),
      let data := shrinkLayerData T s D rem hD small A (K:=K) c branch O
      data.Reads (fun i=>(out i).val) ∧ data.Below (allocate K c (.shrink x)).next.heap (fun i=>(out i).val) ∧
      data.Footprint (fun i=>c.heap≤ i ∧ i<(allocate K c (.shrink x)).next.heap) (fun i=>(out i).val) ∧
      (∀ j,(data.halfWidth j).length≤ stageHalves (.shrink x)) ∧
      (∀ j,(data.motifCopies j).length≤ stageMotifs (.shrink x)) := by
  obtain ⟨old,extra,_⟩:=shrink_scalar_room T s D rem hD small A hu fixed arena wire
  let v:=2^(u^10)
  have uv : u≤v := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_self_pow (by decide) _))
  have big : 2^(16*u^10)=v^16 := by rw [Nat.mul_comm,pow_mul]
  have ov : 1<v := by omega
  obtain ⟨slots,colors,deg,_⟩ := layer_fixed_bounds T s D (fixed.trans uv)
  have bound3 : cap≤v^4 := by
    change 8*d^2*2^paletteSize≤v^4
    calc
      _ ≤ v*v^2*v := by gcongr; omega
      _ = v^4 := by ring
  have bound2 : d*2^paletteSize≤v^2 := (Nat.mul_le_mul slots colors).trans_eq (by ring)
  have bound1 : 2*D≤v^2 := (Nat.mul_le_mul (by omega : 2≤v) deg).trans_eq (by ring)
  have wide : 8≤16*u^10 := by
    have positive : 0<u^10 := Nat.pow_pos (by omega)
    omega
  apply ShrinkOutput.layer_records T s D rem hD small A cur m c branch H old
    ((Nat.le_mul_of_pos_right baseSites (Nat.two_pow_pos t)).trans extra.bases) wide
  · rw [big];exact bound2.trans_lt (Nat.pow_lt_pow_right ov (by decide))
  · rw [big];exact bound3.trans_lt (Nat.pow_lt_pow_right ov (by decide))
  · rw [big];exact bound1.trans_lt (Nat.pow_lt_pow_right ov (by decide))
  · exact offset
  · exact ids

theorem shrink_layer_at_scale {u K : ℕ} (hu : 40≤u) (cur : Word (16*u^10)) (m out : Memory (16*u^10))
    (c : Cursor) (branch : Fin (M).rules.count)
    (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (fixed : shrinkFixedWords T s D≤u) (arena : (Stage.shrink x).heapWords≤2^(u^10))
    (wire : A.maxWidth+1≤(2^(u^10))^4) (offset : 0<c.width)
    (ids : (allocate K c (.shrink x)).next.node≤2^(16*u^10)) :
    ∃ O : ∀v:packSite,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order (ShrinkMotif.chooseWidths (supply branch)) v (16*u^10),
      let data := shrinkLayerData T s D rem hD small A (K:=K) c branch O
      data.Reads (fun i=>(out i).val) ∧ data.Below (allocate K c (.shrink x)).next.heap (fun i=>(out i).val) := by
  obtain ⟨O,read,low,_⟩:=shrink_layer_footprint_at_scale T s D rem hD small A hu cur m out c branch H fixed arena wire offset ids
  exact ⟨O,read,low⟩

private theorem ownerArchiveRange (alphabet : ℕ) (cursor : Cursor) (shape : Dimensions) :
    let entry := allocate alphabet cursor (.shrink shape)
    cursor.heap ≤ entry.words 44 ∧ entry.words 44+shape.originalSites=entry.next.heap ∧
      shape.outputSites ≤ entry.next.heap := by
  simp [allocate,headerExtra,extraEnd]; omega

/-- The old-site indexed owner is a local successor ordinal, in the last descriptor
bank of this allocation. The formula includes the memory read that navigation preserves. -/
theorem shrink_owner_at_scale {u K : ℕ} (hu : 40≤u) (cur : Word (16*u^10)) (m out : Memory (16*u^10))
    (c : Cursor) (branch : Fin (M).rules.count)
    (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (fixed : shrinkFixedWords T s D≤u) (arena : (Stage.shrink x).heapWords≤2^(u^10))
    (wire : A.maxWidth+1≤(2^(u^10))^4) (a : ChildRows.Actual P) :
    let en := allocate K c (.shrink x)
    let read := en.words 44+ChildRows.oldNumber P (B).order a
    (out read).val=Incidents.siteNumber (B).order ((P).placement (ShrinkMotif.chooseWidths (supply branch)) a) ∧
      c.heap≤read ∧ read<en.next.heap := by
  obtain ⟨old,_,_⟩:=shrink_scalar_room T s D rem hD small A hu fixed arena wire
  let W:=16*u^10
  let E:=shrinkOutputCodec s rem A old
  have le : s≤W := ((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp old.slots).le
  have chart (z : BitWord s) : slotCode (w:=W) P z=tagWord le z := Demand.tag_cast le z
  have add (a b : BitWord s) : slotCode (w:=W) P (a+b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_add le a b
  have sub (a b : BitWord s) : slotCode (w:=W) P (a-b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_sub le a b
  let en:=allocate K c (.shrink x)
  have range : c.heap≤en.words 44 ∧ en.words 44+(x).originalSites=en.next.heap ∧ (x).outputSites≤en.next.heap := by
    exact ownerArchiveRange K c x
  have room:=H.cursor.controls.trans_lt cur.isLt
  let lay:=ShrinkMotif.chooseWidths (supply branch)
  have num : Incidents.siteNumber (B).order ((P).placement lay a)<(x).outputSites :=
    DescriptorSpan.site_number_lt (b := (B).order) _
  have reach : ChildRows.oldNumber P (B).order a<(x).originalSites := ChildRows.oldNumber_lt P (B).order a
  have outWord:=PublishedDescriptors.owner_word (S₀:=S) (q:=2*d) («P» := P) (b := (B).order)
    (raw := m) (final := out) (kind := 1) H.records H.cursor H.descHeader H.descInput E
    (fun _=>rfl) add sub old.colors old.slots a
  change out (en.words 44+ChildRows.oldNumber P (B).order a)=(Incidents.siteNumber (B).order ((P).placement lay a):Word W) at outWord
  change (out (en.words 44+ChildRows.oldNumber P (B).order a)).val=_ ∧ _ ∧ _
  rw [outWord,Fin.val_cast_of_lt ((num.trans_le range.2.2).trans room)]
  exact ⟨rfl,range.1.trans (Nat.le_add_right _ _),
    (Nat.add_lt_add_left reach (en.words 44)).trans_eq range.2.1⟩

/-- In the actual ordered list, the preceding prefix of the last numbered half and its
own width account for every outgoing and incoming wire of the site. -/
theorem half_tail_total {N : ℕ} (pos : 0<N) (value : Fin N→ℕ) :
    let last : Fin N := ⟨N-1,Nat.sub_lt pos (by decide : 0 < 1)⟩
    (∑ i : Fin N,if i.val<last.val then value i else 0)+value last=∑ i,value i := by
  intro last
  classical
  calc
    _ = ∑ i : Fin N, ((if i.val<last.val then value i else 0)+(if i=last then value last else 0)) := by
      simp [Finset.sum_add_distrib]
    _ = _ := Finset.sum_congr rfl (fun i _=>by
      by_cases equal : i=last
      · subst i;simp
      · have small : i.val<last.val := by
          have ne : i.val≠last.val := fun eq=>equal (Fin.ext eq)
          have bound:=i.isLt
          change i.val<N-1
          change i.val≠N-1 at ne
          omega
        simp [equal,small])

open private half_base_lower from OAI.ThreeFlat.Diagonal.ShrinkLayerRows
open private halfBankAddress halfEntryAddress from OAI.ThreeFlat.Diagonal.ShrinkNativeHalfRows

set_option maxHeartbeats 1400000 in
theorem shrink_last_half_at_scale {u K : ℕ} (hu : 40≤u) (cur : Word (16*u^10)) (m out : Memory (16*u^10))
    (c : Cursor) (branch : Fin (M).rules.count) (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (fixed : shrinkFixedWords T s D≤u) (arena : (Stage.shrink x).heapWords≤2^(u^10))
    (wire : A.maxWidth+1≤(2^(u^10))^4)
    (j : Fin (x).outputSites) :
    let en:=allocate K c (.shrink x)
    let layer:=nodeLayer K c (.shrink x)
    let ptr:=(out (layer.incident+2*j.val+1)).val
    let last:=2*D-1
    let width:=(out (ptr+4*last+3)).val+(out (ptr+4*last+2)).val
    let z:=(shrinkNextOrder T s D rem hD small A branch).symm j
    width=((M).next branch).incidentWidth (((M).next branch).chart z) ∧
    (∀ O : ∀v:packSite,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order (ShrinkMotif.chooseWidths (supply branch)) v (16*u^10),
      width=((shrinkLayerData T s D rem hD small A (K:=K) c branch O).halfWidth j).sum) ∧
    c.heap≤ptr+4*last+3 ∧ ptr+4*last+3<en.next.heap := by
  let W:=16*u^10
  let V:=2^(u^10)
  let en:=allocate K c (.shrink x)
  let lay:=ShrinkMotif.chooseWidths (supply branch)
  let f:=DescriptorSpan.fields K c x lay
  let X:=(M).next branch
  let z:=(shrinkNextOrder T s D rem hD small A branch).symm j
  let last:Fin (2*D):=⟨2*D-1,by omega⟩
  let val:=fun i:Fin (2*D)=>X.width (Halves.sourceHalf X.graph z i)
  obtain ⟨old,_,_⟩:=shrink_scalar_room T s D rem hD small A hu fixed arena wire
  have positive : 1<V := Nat.one_lt_pow (by positivity) (by decide)
  have big : 2^W=V^16 := by dsimp [V,W];rw [←pow_mul];congr 1;omega
  have uV : u≤V := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_self_pow (by decide) u))
  obtain ⟨_,_,deg,factor⟩ := layer_fixed_bounds T s D (fixed.trans uV)
  have twice : 2*D≤V^2 := (Nat.mul_le_mul (by omega : 2≤V) deg).trans_eq (by ring)
  have fits : 2*D<2^W := by rw [big];exact twice.trans_lt (Nat.pow_lt_pow_right positive (by decide))
  have total : (∑ i,val i)=X.incidentWidth (X.chart z) := by
    have arc (i : Fin D) : X.siteArc (X.chart z, i) = ((z.1, i), z.2) := by
      change (((X.chart.symm (X.chart z)).1, i), (X.chart.symm (X.chart z)).2) = _
      rw [X.chart.symm_apply_apply]
    simp only [State.incidentWidth, arc]
    exact half_total X.graph X.width z
  have priorWidth : 1+A.maxWidth≤V^4 := by
    rw [Nat.add_comm 1 A.maxWidth]
    exact wire
  have nextWire : X.maxWidth≤V^5 :=
    (shrinkBinary_width T s D rem hD small A branch).trans
      ((Nat.mul_le_mul factor priorWidth).trans_eq (show V*V^4=V^5 by ring))
  have allFit : (∑ i,val i)<2^W := by
    rw [total,big]
    exact ((X.incidentWidth_le _).trans ((Nat.mul_le_mul twice nextWire).trans_eq
      (show V^2*V^5=V^7 by ring))).trans_lt (Nat.pow_lt_pow_right positive (by decide))
  have tail : Halves.prefixValue X.graph X.width z last+val last=∑ i,val i :=
    half_tail_total (N := 2*D) (pos := Nat.mul_pos (by decide : 0 < 2) hD) (value := val)
  have graph:=shrink_stored_at T s D rem hD small A branch (shrinkPieceBound s D) H.tagPos _ _ H.descGraph
  have ix : Halves.siteNumber X.order z=j.val := by rw [←shrinkNextOrder_val];exact congrArg Fin.val ((shrinkNextOrder T s D rem hD small A branch).apply_symm_apply j)
  have payload (col : Fin 4) :=
    PublishedDescriptors.half_word («S» := S) H.records H.cursor H.descHeader X.graph X.order X.width
      graph rfl rfl fits old.residual z last col (ix.trans_lt j.isLt)
  have widthFits : val last<2^W := by omega
  have prefixFits : Halves.prefixValue X.graph X.width z last<2^W := by omega
  obtain ⟨_,hf,_,_,_,_,we,_⟩ := shrink_allocated_fields T s D rem hD small A (K:=K) c branch
  have endFit : en.next.heap < 2^W := H.cursor.controls.trans_lt cur.isLt
  have stop : f 40+(8*D)*(x).outputSites ≤ en.next.heap := we
  have bottom : c.heap ≤ f 40 := (half_base_lower K c x lay).2
  let pointer := (out ((nodeLayer K c (.shrink x)).incident+2*j.val+1)).val
  have ptr : pointer = f 40+j.val*(8*D) := by
    have hp := PublishedDescriptors.half_header_word («S» := S) H.records H.cursor H.descHeader j 1
    change out (f 38+(2*j.val+1))=((f 40+j.val*(8*D):ℕ):Word W) at hp
    have address : (nodeLayer K c (.shrink x)).incident+2*j.val+1 = f 38+(2*j.val+1) := by
      exact (congrArg (fun a : ℕ => a+2*j.val+1) hf.symm).trans (Nat.add_assoc ..)
    have bound := (halfBankAddress bottom stop j.isLt (show 0 < 8*D by omega)).2.trans endFit
    have fit : f 40+j.val*(8*D)<2^W := by simpa only [Nat.add_zero] using bound
    exact (congrArg (fun a : ℕ => (out a).val) address).trans ((congrArg Fin.val hp).trans (Fin.val_cast_of_lt fit))
  have addr (q : ℕ) : pointer+4*last.val+q =
      f 40+((Halves.siteNumber X.order z*(2*D)+last.val)*4+q) := by
    rw [ptr, ix]
    ring
  have wd : (out (pointer+4*last.val+2)).val = val last :=
    ((congrArg (fun a : ℕ => (out a).val) (addr 2)).trans (congrArg Fin.val (payload 2))).trans
      (Fin.val_cast_of_lt widthFits)
  have pf : (out (pointer+4*last.val+3)).val = Halves.prefixValue X.graph X.width z last :=
    ((congrArg (fun a : ℕ => (out a).val) (addr 3)).trans (congrArg Fin.val (payload 3))).trans
      (Fin.val_cast_of_lt prefixFits)
  have widthSum := (congrArg₂ Nat.add pf wd).trans tail
  refine ⟨widthSum.trans total, ?_, halfEntryAddress bottom stop j.isLt last.isLt (by decide : 3 < 4) ptr⟩
  intro O
  exact widthSum.trans (by simp only [shrinkLayerData, List.sum_ofFn, val, X, z])


set_option maxHeartbeats 1600000 in
/-- All numbered physical half descriptors and both of their allocation spans, read
from the actual selected shrink producer. -/
theorem shrink_half_rows_at_scale {u K : ℕ} (hu : 40≤u) (cur : Word (16*u^10)) (m out : Memory (16*u^10))
    (c : Cursor) (branch : Fin (M).rules.count) (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (fixed : shrinkFixedWords T s D≤u) (arena : (Stage.shrink x).heapWords≤2^(u^10))
    (wire : A.maxWidth+1≤(2^(u^10))^4) :
    let O:=shrinkArchiveSites (K:=K) T s D rem hD small A c branch
    State.HalfRows O (fun i=>c.heap≤ i ∧ i<(allocate K c (.shrink x)).next.heap) (fun i=>(out i).val) := by
  let W:=16*u^10
  let V:=2^(u^10)
  let X:=(M).next branch
  let O:=shrinkArchiveSites (K:=K) T s D rem hD small A c branch
  let en:=allocate K c (.shrink x)
  let f:=DescriptorSpan.fields K c x (ShrinkMotif.chooseWidths (supply branch))
  have bound : en.next.heap<2^W := H.cursor.controls.trans_lt cur.isLt
  obtain ⟨old,_,_⟩:=shrink_scalar_room T s D rem hD small A hu fixed arena wire
  have pos : 1<V := Nat.one_lt_pow (by positivity) (by decide)
  have large : 2^W=V^16 := by dsimp [V,W];rw [←pow_mul];congr 1;omega
  have uV : u≤V := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_self_pow (by decide) u))
  obtain ⟨_,_,deg,factor⟩ := layer_fixed_bounds T s D (fixed.trans uV)
  have wireScale : 1 + A.maxWidth ≤ V^4 := by
    rw [Nat.add_comm 1 A.maxWidth]
    exact wire
  have ceil : X.maxWidth≤V^5 :=
    (shrinkBinary_width T s D rem hD small A branch).trans ((Nat.mul_le_mul factor
      wireScale).trans_eq (show V*V^4=V^5 by ring))
  have twice : 2*D≤V^2 := (Nat.mul_le_mul (by omega : 2≤V) deg).trans_eq (by ring)
  have df : 2*D<2^W := by rw [large];exact twice.trans_lt (Nat.pow_lt_pow_right pos (by decide))
  have widthFit (e) : X.width e < 2^W := by
    rw [large]
    exact ((X.width_le_maxWidth e).trans ceil).trans_lt (Nat.pow_lt_pow_right pos (by decide))
  have prefixFit (z) (i) : Halves.prefixValue X.graph X.width z i<2^W := by
    have h : Halves.prefixValue X.graph X.width z i≤∑ k : Fin (2*D),X.width (Halves.sourceHalf X.graph z k) := by
      unfold Halves.prefixValue
      apply Finset.sum_le_sum
      intro j _
      split
      · exact le_rfl
      · exact Nat.zero_le _
    have total : (∑ k : Fin (2*D),X.width (Halves.sourceHalf X.graph z k))=X.incidentWidth (X.chart z) := by
      have arc (i : Fin D) : X.siteArc (X.chart z, i) = ((z.1, i), z.2) := by
        change (((X.chart.symm (X.chart z)).1, i), (X.chart.symm (X.chart z)).2) = _
        rw [X.chart.symm_apply_apply]
      simp only [State.incidentWidth, arc]
      exact half_total X.graph X.width z
    rw [total] at h
    rw [large]
    exact (h.trans ((X.incidentWidth_le _).trans ((Nat.mul_le_mul twice ceil).trans_eq
      (show V^2*V^5=V^7 by ring)))).trans_lt (Nat.pow_lt_pow_right pos (by decide))
  exact shrink_half_rows_of_bounds T s D rem hD small A cur m out c branch H df old.residual widthFit prefixFit


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
