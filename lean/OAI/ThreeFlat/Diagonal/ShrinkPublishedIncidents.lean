import OAI.ThreeFlat.Diagonal.ShrinkPublishedChildren
import OAI.ThreeFlat.Diagonal.CompressorIncidentColumns

namespace OAI
/-! # The live and zero-padded motif rows in the retained site directory -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan RAM.HeaderScan RAM.PhysicalPinsExpr
open NavigationDirectory Resident Placement Incidents
open scoped Classical Fin.NatCast
variable {w N K kind t l : ℕ} {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {S : Graph.Stage}
variable {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors} {b : B ≃ Fin N}
variable {hc : 2≤S.colors} {lay : Bool} {c : Cursor} {cur : Word w} {raw old final : Memory w}
set_option quotPrecheck false
local notation "x" => dims S N t l
local notation "f" => fields K c x lay
local notation "p" => pointers K c x
local notation "extra" => ((p).costs+2*((x).motifs+1))
local notation "tail" => (allocate K c (.shrink x)).next.heap
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors→ℕ} {supply : P.Motif → Fin 8 → ℕ}
variable (pub : PublishedDescriptors S K c (dims S N t l) lay cur kind old final)
variable (space : CursorSpace cur raw c K (dims S N t l)) (head : Scans.Header cur old c.header 63 (fields K c (dims S N t l) lay))
variable (I : Input S P b hc lay (pointers K c (dims S N t l)) cur prior supply old) (E : Codec B w S.colors t l)
variable (code : ∀v,E.base v=((b v).val:Word w))
variable (add : ∀u v,slotCode (w:=w) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
variable (sub : ∀u v,slotCode (w:=w) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
variable (baseFit : N≤2^w) (tagFit : 2^t<2^w) (laneFit : 2^l<2^w) (bits : 2^S.colors<2^w)
variable (masks : 8≤w) (cap : Incidents.capacity S<2^w) (offset : 0<(pointers K c (dims S N t l)).oldWidths)
variable (site : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))
local notation "count" => (siteKeys (w:=w) P b lay site).length
local notation "ord" => denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc
local notation "start" => Incidents.capacity S*Incidents.siteNumber b site
local notation "D" => Incidents.descriptor P b Template.ptr (fun _=>cur) old (fun _=>0) hc K lay site

open scoped Fin.CommRing in
private theorem choice_addresses (width base row : ℕ) :
    (base : Word width)+(row : Word width)*3=((base+3*row : ℕ) : Word width) ∧
    (base : Word width)+(row : Word width)*3+1=((base+3*row+1 : ℕ) : Word width) := by
  constructor <;> simp only [Nat.mul_comm 3 row,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]

include space head in
omit [Fintype B] [Fintype H] in
theorem descriptor_agree {alt : Memory w} (frame : agreesOutside extra tail alt old)
    (vs : Fin 1→Word w) (z : P.Motif) :
    Incidents.descriptor P b Template.ptr (fun _=>cur) alt vs hc K lay site z=D z := by
  let i:=(ord z).val
  have inside : i<(x).motifs := (ord z).isLt
  have stop : (p).choices+3*(x).motifs≤extra := by simp [pointers,allocate,headerWord]; omega
  have maxEnd : extra≤tail := by simp [pointers,allocate,headerWord,extraEnd,headerExtra]; omega
  have fit : (p).choices+3*i+1<2^w := by
    have hi:=(maxEnd.trans space.controls).trans_lt cur.isLt;omega
  have h:=descriptor_field_frame space head frame
  have cmd (m : Memory w) (vs : Fin 1→Word w) (hdr : Scans.Header cur m c.header 63 f) :
      Formula.value (fun _=>cur) m vs (Template.f choiceTable)=((p).choices:Word w) ∧
      Formula.value (fun _=>cur) m vs (Template.f countTable)=((p).counts:Word w) :=
    ⟨field_word hdr vs 2 (by decide),field_word hdr vs 1 (by decide)⟩
  obtain ⟨address0,address1⟩:=choice_addresses w (p).choices i
  have first : (((p).choices:Word w)+(i:Word w)*3).val=(p).choices+3*i := by
    rw [address0,Fin.val_cast_of_lt (by omega)]
  have second : (((p).choices:Word w)+(i:Word w)*3+1).val=(p).choices+3*i+1 := by
    rw [address1,Fin.val_cast_of_lt fit]
  have saved0:=descriptor_choice_frame space frame (a:=(p).choices+3*i) (by constructor <;> omega)
  have saved1:=descriptor_choice_frame space frame (a:=(p).choices+3*i+1) (by constructor <;> omega)
  simp only [Incidents.descriptor,(cmd alt vs h).1,(cmd alt vs h).2,(cmd old (fun _=>0) head).1,
    (cmd old (fun _=>0) head).2,←show i=(ord z).val from rfl,first,second,saved0,saved1]

include I offset in
omit [Fintype B] [Fintype H] in
private theorem keys_identify (O Q : SiteOrder P b lay site w) (i : Fin count) : (O.equiv i).val=(Q.equiv i).val := by
  apply positiveKey_inj P b _ ((O.key_eq i).symm.trans (Q.key_eq i))
  intro a
  have bound:=(Nat.add_lt_add_left (SlotImage.edgeOrdinal_lt b (Demand.laneOrdinal P)
    (packedAddress.symm a)) (p).oldWidths).trans_le I.widthBound
  rw [Demand.edge_address] at bound
  omega

omit [Fintype B] in
private theorem row_range (i : ℕ) (j : Fin 6) (hi : i<Incidents.capacity S) :
    6*(start+i)+j.val<f 37 ∧ f 36+(6*(start+i)+j.val)<tail := by
  have s : Incidents.siteNumber b site<(x).outputSites:=site_number_lt site
  have r:=half_index_lt (half_index_lt s hi) j.isLt
  have under : 6*(start+i)+j.val<f 37 := by
    change _<6*Incidents.capacity S*(x).outputSites
    convert r using 1 <;> ring
  have finish : f 36+f 37≤tail := by simp [fields,allocate,extraEnd,headerExtra]; omega
  exact ⟨under,(Nat.add_lt_add_left under _).trans_le finish⟩

include pub space head I E code add sub baseFit tagFit laneFit bits masks cap offset in
omit [Fintype B] [Fintype H] in
theorem PublishedDescriptors.incident_words :
    ∃ O : SiteOrder P b lay site w,count≤Incidents.capacity S ∧
      (∀ (i : Fin count) (j : Fin 6),final (f 36+(6*(start+i.val)+j.val))=D (O.equiv i).val j) ∧
      (∀ (i : ℕ) (j : Fin 6),count≤ i → i<Incidents.capacity S →
        final (f 36+(6*(start+i)+j.val))=0) := by
  obtain ⟨O,sz,_⟩:=I.incident_site E code add sub baseFit tagFit laneFit bits masks cap offset K site
  refine ⟨O,sz,?_,?_⟩
  · intro i j
    have range:=row_range (b:=b) (K:=K) (c:=c) (lay:=lay) site i.val j (i.isLt.trans_le sz)
    apply (pub.incident range.1).read range.2
    intro m frame
    let idx:=6*(start+i.val)+j.val
    let vs:=fun _ : Fin 1=>((f 36+idx:ℕ):Word w)
    have H:=descriptor_field_frame space head frame
    have R:=descriptor_input_frame space I frame
    have fits:=(range.2.trans_le space.controls).trans cur.isLt
    have atIx : (Formula.value (fun _=>cur) m vs (NodeRecipe.offset 36)).val=idx := by
      rw [offset_word H 36 idx (by decide) fits,Fin.val_cast_of_lt (by omega)]
    obtain ⟨Q,_,_,live,_⟩:=R.incident_site E code add sub baseFit tagFit laneFit bits masks cap offset K site
    rw [NodeRecipe.motif,selected_word H vs,NodeRecipe.incidentBase,live vs _ i j atIx,descriptor_agree space head site frame vs,
      keys_identify I offset site Q O i]
  · intro i j lehi hi
    have range:=row_range (b:=b) (K:=K) (c:=c) (lay:=lay) site i j hi
    apply (pub.incident range.1).read range.2
    intro m frame
    let idx:=6*(start+i)+j.val
    let vs:=fun _ : Fin 1=>((f 36+idx:ℕ):Word w)
    have H:=descriptor_field_frame space head frame
    have R:=descriptor_input_frame space I frame
    have fits:=(range.2.trans_le space.controls).trans cur.isLt
    have atIx : (Formula.value (fun _=>cur) m vs (NodeRecipe.offset 36)).val=idx := by
      rw [offset_word H 36 idx (by decide) fits,Fin.val_cast_of_lt (by omega)]
    obtain ⟨_,_,_,_,idle⟩:=R.incident_site E code add sub baseFit tagFit laneFit bits masks cap offset K site
    rw [NodeRecipe.motif,selected_word H vs,NodeRecipe.incidentBase,idle vs _ i j lehi hi atIx]

include pub space head I E code add sub baseFit tagFit laneFit bits masks cap offset in
omit [Fintype B] [Fintype H] in
theorem PublishedDescriptors.kernel_words (col : Fin 5) :
    let n:=Incidents.siteNumber b site
    final (f 34+(5*n+col.val))=
      ((![c.header,n,kind,count,f 36+n*(6*Incidents.capacity S)] : Fin 5→ℕ) col:Word w) := by
  let n:=Incidents.siteNumber b site
  let ix:=5*n+col.val
  have s : n<(x).outputSites:=site_number_lt site
  have indexBound : ix<f 35 := by
    change 5*n+col.val<5*(x).outputSites
    simpa only [Nat.mul_comm 5] using half_index_lt s col.isLt
  have end0 : f 34+f 35≤tail := by simp [fields,allocate,extraEnd,headerExtra]; omega
  have bound:=(Nat.add_lt_add_left indexBound (f 34)).trans_le end0
  have fit:=(bound.trans_le space.controls).trans cur.isLt
  apply (pub.kernel indexBound).read bound
  intro m frame
  let vs:=fun _ : Fin 1=>((f 34+ix:ℕ):Word w)
  let V:=Formula.value (fun _=>cur) m vs
  let pos:=NodeRecipe.offset 34
  let siteF:=Formula.op .div pos (.lit 5)
  let fieldF:=Formula.op .mod pos (.lit 5)
  have H:=descriptor_field_frame space head frame
  have R:=descriptor_input_frame space I frame
  have five : 5<2^w := by have:=H.fit;omega
  have lits (i : ℕ) (hi : i≤5) : (V (.lit i)).val=i:=Fin.val_cast_of_lt (by omega)
  have lin : (V pos).val=ix :=
    (congrArg Fin.val (offset_word H 34 ix (by decide) fit)).trans
      (Fin.val_cast_of_lt ((Nat.le_add_left ix (f 34)).trans_lt fit))
  have sn : (V siteF).val=n := by
    have divRead : (V siteF).val=(V pos).val/(V (.lit 5)).val :=
      Incidents.div_value (fun _=>cur) m vs pos (.lit 5)
    rw [divRead,lin,lits 5 (by decide)]
    change (5*n+col.val)/5=n
    rw [Nat.mul_add_div (by decide : 0<5),Nat.div_eq_of_lt col.isLt,Nat.add_zero]
  have fld : (V fieldF).val=col.val := by
    have modRead : (V fieldF).val=(V pos).val%(V (.lit 5)).val :=
      Incidents.mod_value (fun _=>cur) m vs pos (.lit 5)
    rw [modRead,lin,lits 5 (by decide)]
    change (5*n+col.val)%5=col.val
    rw [Nat.mul_add_mod,Nat.mod_eq_of_lt col.isLt]
  have snW : V siteF=(n:Word w) := by rw [←sn,Fin.cast_val_eq_self]
  have hdr : V (.load Template.ptr)=(c.header:Word w) := by
    change m cur.val=_;rw [←H.pointer,Fin.cast_val_eq_self]
  obtain ⟨_,_,countAt,_⟩:=R.incident_site E code add sub baseFit tagFit laneFit bits masks cap offset K site
  have counted : V (NodeRecipe.selectedAt (fun l=>Incidents.count Template.ptr S K l siteF))=(count:Word w) := by
    exact (selected_word H vs (fun side=>Incidents.count Template.ptr S K side siteF)).trans
      ((Fin.cast_val_eq_self (V (Incidents.count Template.ptr S K lay siteF))).symm.trans
        (congrArg (fun a : ℕ => (a : Word w)) (countAt vs siteF sn)))
  have address : V (.op .add (Template.f 36) (.op .mul siteF (.lit (6*Incidents.capacity S))))=
      ((f 36+n*(6*Incidents.capacity S):ℕ):Word w) := by
    change V (Template.f 36)+V siteF*((6*Incidents.capacity S:ℕ):Word w)=_
    have fieldWord : V (Template.f 36)=(f 36:Word w) := field_word H vs 36 (by decide)
    rw [fieldWord,snW,Nat.cast_add]
    apply congrArg (fun z : Word w => (f 36:Word w)+z)
    exact Fin.ext (Nat.mul_mod n (6*Incidents.capacity S) (2^w)).symm
  have test (k : ℕ) (hk : k≤4) : (V fieldF == V (.lit k))=decide (col.val=k) := by
    have eqv : V fieldF=V (.lit k) ↔ col.val=k := by
      rw [Fin.ext_iff,fld,lits k (by omega)]
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq,decide_eq_true_eq] using eqv
  change (if V fieldF == V (.lit 0) then V (.load Template.ptr) else
    if V fieldF == V (.lit 1) then V siteF else
    if V fieldF == V (.lit 2) then (kind:Word w) else
    if V fieldF == V (.lit 3) then V (NodeRecipe.selectedAt (fun l=>Incidents.count Template.ptr S K l siteF))
    else V (.op .add (Template.f 36) (.op .mul siteF (.lit (6*Incidents.capacity S)))))=_
  rw [test 0 (by decide),test 1 (by decide),test 2 (by decide),test 3 (by decide),hdr,snW,counted,address]
  fin_cases col <;> rfl



end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan

end OAI
