import OAI.ThreeFlat.Diagonal.ShrinkDescriptorContext
import OAI.ThreeFlat.Diagonal.CompressorHalfFits
import OAI.ThreeFlat.Diagonal.CompressorPhysicalWidthRow

namespace OAI
/-! # Physical values of the retained outgoing and incoming half-port rows -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.DescriptorScan RAM.PhysicalPinsExpr
open RAM.DescriptorExpr NavigationDirectory Resident
open scoped Fin.NatCast
variable {w K kind : ℕ} {c : Cursor} {x : Dimensions} {S : Graph.Stage} {cur : Word w}
variable {layout : Bool} {raw old final : Memory w}
set_option quotPrecheck false
local notation "f" => fields K c x layout
local notation "p" => pointers K c x
local notation "tail" => (allocate K c (.shrink x)).next.heap
local notation "C" => (⟨(p).newGraph,x.newEdges,(p).newWidths⟩ : SlotImage.Columns)

theorem field_word {m : Memory w} (h : Scans.Header cur m c.header 63 f) (vs : Fin 1 → Word w)
    (i : ℕ) (hi : i≤63) : Formula.value (fun _=>cur) m vs (Template.f i)=(f i:Word w) := by
  change headerRead m cur i=_
  rw [←h.get i hi,Fin.cast_val_eq_self]
  rfl

theorem offset_word {m : Memory w} (h : Scans.Header cur m c.header 63 f)
    (i j : ℕ) (hi : i≤63) (room : f i+j<2^w) :
    Formula.value (fun _=>cur) m (fun _ : Fin 1=>((f i+j:ℕ):Word w)) (NodeRecipe.offset i)=(j:Word w) := by
  apply Template.cut_index
  · exact room
  · exact field_word h _ _ hi
  · rfl

theorem selected_word {m : Memory w} (h : Scans.Header cur m c.header 63 f) (vs : Fin 1 → Word w)
    (g : Bool→Template.F) : Formula.value (fun _=>cur) m vs (NodeRecipe.selectedAt g)=
      Formula.value (fun _=>cur) m vs (g layout) := by
  let V:=Formula.value (fun _=>cur) m vs
  have sel : V (Template.f selected)=if layout then 1 else 0 := by
    rw [show V (Template.f selected)=(f 27:Word w) from field_word h vs 27 (by decide)]
    cases layout <;> rfl
  have one : (1:Word w)≠0 := by
    intro eqv
    have vv:=congrArg Fin.val eqv
    have bound : 1<2^w := by have:=h.fit;omega
    have v : (1:Word w).val=1 := Fin.val_cast_of_lt bound
    rw [v] at vv;contradiction
  change (if Comparison.eq.test (V (Template.f selected)) (1:Word w) then V (g true) else V (g false))=_
  cases layout <;> simp [sel,Comparison.test,Ne.symm one] <;> rfl

theorem half_index_lt {i j n r : ℕ} (lt : i<n) (small : j<r) : i*r+j<n*r := by
  calc i*r+j < i*r+r := Nat.add_lt_add_left small _
       _ = (i+1)*r := (Nat.succ_mul ..).symm
       _ ≤ n*r := Nat.mul_le_mul_right r lt

theorem PublishedDescriptors.half_word {B : Type} {t N : ℕ} (pub : PublishedDescriptors S K c x layout cur kind old final)
    (space : CursorSpace cur raw c K x) (H : Scans.Header cur old c.header 63 f)
    (G : LiftedSlots B S.outputDegree (BitWord t)) (b : B ≃ Fin N)
    (width : SlotImage.Edge B (BitWord t) S.outputDegree→ℕ)
    (g : SlotImage.Stored G b (tagOrdinal t) C (fun i=>(old i).val) width)
    (deg : x.newDegree=S.outputDegree) (lanes : x.residual=2^t)
    (degreeRoom : 2*S.outputDegree<2^w) (laneRoom : 2^t<2^w)
    (u : B × BitWord t) (j : Fin (2*S.outputDegree)) (col : Fin 4)
    (site : Halves.siteNumber b u<x.outputSites) :
    let offset:=(Halves.siteNumber b u*(2*S.outputDegree)+j.val)*4+col.val
    let e:=Halves.sourceHalf G u j
    final (f 40+offset)=((![Halves.edgeNumber b e,if j.val<S.outputDegree then 0 else 1,width e,
      Halves.prefixValue G width u j] : Fin 4→ℕ) col:Word w) := by
  let off:=(Halves.siteNumber b u*(2*S.outputDegree)+j.val)*4+col.val
  have bound : off<f 41 := by
    have r:=half_index_lt (half_index_lt site j.isLt) col.isLt
    change off<8*x.newDegree*x.outputSites
    rw [deg];dsimp only [off];convert r using 1; ring
  have lim : f 40+f 41≤tail := by simp [fields,allocate,headerExtra,extraEnd]; omega
  have addr : f 40+off<tail := (Nat.add_lt_add_left bound _).trans_le lim
  have room:=(addr.trans_le space.controls).trans cur.isLt
  apply (pub.half bound).read addr
  intro m frame
  let N₀:=fun i=>(m i).val
  let vs:=fun _ : Fin 1=>((f 40+off:ℕ):Word w)
  let data:=fun _ : Param=>cur.val
  let vals:=fun i=>(vs i).val
  let V:=Formula.natural w data N₀ vals
  let Fit:=Formula.Fits w data N₀ vals
  let q:=Halves.shrinkColumns Template.ptr
  let y:=NodeRecipe.offset 40
  have head:=descriptor_field_frame space H frame
  have phy:=descriptor_graph_frame g lanes.symm frame
  have natural (i : ℕ) (hi : i≤63) : V (Template.f i)=f i := by
    change (m ((m cur.val).val+i)).val=_
    rw [head.pointer];exact head.values i hi
  have safe (i : ℕ) (hi : i≤63) : Fit (Template.f i) := by
    refine ⟨⟨⟨trivial,cur.isLt⟩,trivial,trivial⟩,?_⟩
    change (m cur.val).val+i<2^w
    rw [head.pointer];have:=head.fit;omega
  have colMap : q.layout V=⟨2^t,(C).graph,(C).rows,(C).widths⟩ := by
    change Halves.Layout.mk (V (Template.f 14)) (V (Template.f 20)) (V (Template.f 22)) (V (Template.f 24))=_
    rw [natural 14 (by decide),natural 20 (by decide),natural 22 (by decide),natural 24 (by decide)]
    exact congrArg (fun n => Halves.Layout.mk n (C).graph (C).rows (C).widths) lanes
  have table : Halves.Stored G b (q.layout V) N₀ width := colMap.symm ▸ SlotImage.forHalves phy
  have ge : (C).graph+6*(C).rows≤2^w := by
    have e:=space.separation.graphEnd
    exact e.le
  have we : (C).widths+N*S.outputDegree*2^t≤2^w := by
    rw [←g.rowCount,←lanes];exact space.end_lt.le
  have small : 4<2^w := by have:=head.fit;omega
  have reg : Halves.Region (W:=w) data N₀ vals q N S.outputDegree t := by
    refine ⟨⟨safe 14 (by decide),safe 20 (by decide),safe 22 (by decide),safe 24 (by decide)⟩,?_,?_,?_,degreeRoom,laneRoom⟩
    · exact (natural 22 (by decide)).trans g.rowCount
    · change V (Template.f 20)+6*(N*S.outputDegree)≤_
      rw [natural 20 (by decide),←g.rowCount]
      exact ge
    · change V (Template.f 24)+N*S.outputDegree*2^t≤_
      rw [natural 24 (by decide)];exact we
  have atArg : vals 0=f 40+off := Fin.val_cast_of_lt room
  have index : V y=off := by
    change vals 0-V (Template.f 40)=_
    rw [atArg,natural 40 (by decide)];omega
  have baseFit : V (Template.f 40)<2^w :=
    (natural 40 (by decide)).trans_lt ((Nat.le_add_right (f 40) off).trans_lt room)
  have indexFit : Fit y := ⟨trivial,safe 40 (by decide),(vs 0).isLt,baseFit⟩
  have ix : V y<2^w := by rw [index];omega
  have checked:=Halves.record_fits data N₀ vals q table reg y u j col indexFit ix small index
  have read:=Halves.record_read w data N₀ vals q table y u j col index
  have word:=Formula.value_eq_natural (Halves.record q S.outputDegree y) data N₀ vals checked
  change Formula.value (fun _=>cur) m vs (Halves.record q S.outputDegree y)=_
  simpa only [data,N₀,vals,Fin.cast_val_eq_self] using
    word.trans (congrArg (fun a : ℕ => (a : Word w)) read)

/-- The geometric successor keeps its pre-cast degree when selecting a half.
Its physical table uses the equal public degree from the stage header. -/
theorem PublishedDescriptors.half_prefix_of_degree {B : Type} {t N d : ℕ}
    (pub : PublishedDescriptors S K c x layout cur kind old final)
    (space : CursorSpace cur raw c K x) (H : Scans.Header cur old c.header 63 f)
    (G : LiftedSlots B d (BitWord t)) (b : B≃Fin N) (width : SlotImage.Edge B (BitWord t) d→ℕ)
    (g : SlotImage.Stored G b (tagOrdinal t) C (fun i=>(old i).val) width)
    (degree : d=S.outputDegree) (deg : x.newDegree=S.outputDegree) (lanes : x.residual=2^t)
    (degreeRoom : 2*S.outputDegree<2^w) (laneRoom : 2^t<2^w)
    (u:B×BitWord t) (j:Fin (2*d)) (site:Halves.siteNumber b u<x.outputSites) :
    final (f 40+((Halves.siteNumber b u*(2*S.outputDegree)+j.val)*4+3))=
      (Halves.prefixValue G width u j:Word w) := by
  subst d
  exact pub.half_word space H G b width g deg lanes degreeRoom laneRoom u j 3 site

theorem PublishedDescriptors.half_header_word (pub : PublishedDescriptors S K c x layout cur kind old final)
    (space : CursorSpace cur raw c K x) (H : Scans.Header cur old c.header 63 f)
    (s : Fin x.outputSites) (col : Fin 2) :
    final (f 38+(2*s.val+col.val))=
      ((![2*S.outputDegree,f 40+s.val*(8*S.outputDegree)] : Fin 2→ℕ) col:Word w) := by
  let ix:=2*s.val+col.val
  have under : ix<f 39 := by
    have r:=half_index_lt s.isLt col.isLt
    change 2*s.val+col.val<2*x.outputSites
    omega
  have end0 : f 38+f 39≤tail := by simp [fields,allocate,headerExtra,extraEnd]; omega
  have bound:=(Nat.add_lt_add_left under (f 38)).trans_le end0
  have fit:=(bound.trans_le space.controls).trans cur.isLt
  apply (pub.halfHeader under).read bound
  intro m frame
  let vs:=fun _ : Fin 1=>((f 38+ix:ℕ):Word w)
  let V:=Formula.value (fun _=>cur) m vs
  let pos:=NodeRecipe.offset 38
  let row:=Formula.op .div pos (.lit 2)
  let index:=Formula.op .mod pos (.lit 2)
  have h:=descriptor_field_frame space H frame
  have two : 2<2^w := by have:=h.fit;omega
  have radix : (V (.lit 2)).val=2:=Fin.val_cast_of_lt two
  have off : V pos=(ix:Word w) := offset_word h 38 ix (by decide) fit
  have arg : (V pos).val=ix := by rw [off,Fin.val_cast_of_lt (by omega)]
  have site : (V row).val=s.val := by
    dsimp only [row]
    rw [Incidents.div_value,arg,radix]
    dsimp only [ix]
    omega
  have bit : (V index).val=col.val := by
    dsimp only [index]
    rw [Incidents.mod_value,arg,radix]
    dsimp only [ix]
    omega
  have vsite : V row=(s.val:Word w) := by rw [←site,Fin.cast_val_eq_self]
  have test : Comparison.eq.test (V index) (0:Word w)=decide (col.val=0) := by
    have eqv : V index=0 ↔ col.val=0 := by rw [Fin.ext_iff,bit,Fin.val_zero]
    apply Bool.eq_iff_iff.mpr
    simpa only [Comparison.test,beq_iff_eq,decide_eq_true_eq] using eqv
  have baseWord : V (Template.f 40)=(f 40:Word w) := field_word h vs 40 (by decide)
  change (if Comparison.eq.test (V index) (0:Word w) then ((2*S.outputDegree:ℕ):Word w) else
    V (Template.f 40)+V row*((8*S.outputDegree:ℕ):Word w))=_
  rw [test,baseWord,vsite]
  fin_cases col <;> simp [Nat.cast_add]
  exact Fin.ext (Nat.mul_mod s.val (8*S.outputDegree) (2^w)).symm



end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan

end OAI
