import OAI.ThreeFlat.Diagonal.ShrinkNativeChild

namespace OAI
/-! # Both directions of the retained shrinking-stage ownership directory -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan RAM.HeaderScan RAM.PhysicalPinsExpr
open NavigationDirectory Resident Placement
open scoped Classical Fin.NatCast
variable {w N d K kind t l q : ℕ} {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H]
variable (S₀ : Graph.Stage)
set_option quotPrecheck false
local notation "childStage" => ChildRows.withFree S₀ q
local notation "x" => dims childStage N t l
local notation "deg" => S₀.degree
variable {P : PackingData B H (BitWord t) (BitWord l) S₀.degree (q+1)} {b : B ≃ Fin N}
variable {hc : 2≤q+1} {lay : Bool} {c : Cursor} {cur : Word w} {raw old final : Memory w}
local notation "f" => fields K c x lay
local notation "p" => pointers K c x
local notation "tail" => (allocate K c (.shrink x)).next.heap
variable {prior : Arc B H (BitWord t) (BitWord l) S₀.degree (q+1)→ℕ} {supply : P.Motif → Fin 8 → ℕ}
variable (pub : PublishedDescriptors (ChildRows.withFree S₀ q) K c (dims (ChildRows.withFree S₀ q) N t l) lay cur kind old final)
variable (space : CursorSpace cur raw c K (dims (ChildRows.withFree S₀ q) N t l)) (head : Scans.Header cur old c.header 63 (fields K c (dims (ChildRows.withFree S₀ q) N t l) lay))
variable (I : Input (ChildRows.withFree S₀ q) P b hc lay (pointers K c (dims (ChildRows.withFree S₀ q) N t l)) cur prior supply old) (E : Codec B w (q+1) t l)
variable (code : ∀v,E.base v=((b v).val:Word w))
variable (add : ∀u v,slotCode (w:=w) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
variable (sub : ∀u v,slotCode (w:=w) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))

theorem field_nat {X : Dimensions} {m : Memory w} (h : Scans.Header cur m c.header 63 (fields K c X lay))
    (vs : Fin 1→Word w) (i : ℕ) (hi : i≤63) :
    (Formula.value (fun _=>cur) m vs (Template.f i)).val=fields K c X lay i :=
  h.get i hi

include pub space head I E code add sub in
omit [Fintype B] [Fintype H] in
theorem PublishedDescriptors.owner_word (bits : 2^(q+1)<2^w) (degree : deg<2^w)
    (u : ChildRows.Actual P) :
    final (f 44+ChildRows.oldNumber P b u)=(Incidents.siteNumber b (P.placement lay u):Word w) := by
  let i:=ChildRows.oldNumber P b u
  have hi : i<f 45 := ChildRows.oldNumber_lt P b u
  have end0 : f 44+f 45=tail:=rfl
  have bound : f 44+i<tail:=(Nat.add_lt_add_left hi _).trans_eq end0
  have fit:=(bound.trans_le space.controls).trans cur.isLt
  apply (pub.owner hi).read bound
  intro m frame
  let vs:=fun _ : Fin 1=>((f 44+i:ℕ):Word w)
  have h:=descriptor_field_frame space head frame
  have stored:=descriptor_input_frame space I frame
  have R:=stored.arc E vs code add sub
  rw [NodeRecipe.ownerBase,selected_word h vs]
  apply ChildRows.parent_code (S:=childStage) P b E cur m vs code bits degree lay R.toGraphReads _ u
  · rw [offset_word h 44 i (by decide) fit,Fin.val_cast_of_lt (by omega)]
  · exact field_nat h vs 26 (by decide)
  · exact field_nat h vs 15 (by decide)
  · exact field_nat h vs 14 (by decide)

omit [Fintype B] in
theorem site_number_lt (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l)) :
    Incidents.siteNumber b s<N*2^t*2^l := by
  have first:=half_index_lt (b s.1).isLt (tagOrdinal t s.2.1).isLt
  have second:=half_index_lt first (tagOrdinal l s.2.2).isLt
  unfold Incidents.siteNumber
  convert second using 1; ring

include pub space head I E code add sub in
omit [Fintype B] [Fintype H] in
theorem PublishedDescriptors.child_word (degree : deg<2^w) (capFits : deg*2^(q+1)<2^w) (bitsFit : 2^q<2^w)
    (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l)) (j : Fin (deg*2^(q+1))) :
    let child:=(Owner.childOrder P lay s j).val
    let i:=Incidents.siteNumber b s*(deg*2^(q+1))+j.val
    final (f 42+i)=((c.node+ChildRows.oldNumber P b child:ℕ):Word w) := by
  let child:=Owner.childOrder P lay s j
  let i:=Incidents.siteNumber b s*(deg*2^(q+1))+j.val
  have hi : i<f 43 := by
    have site:=site_number_lt (b:=b) s
    have upper:=half_index_lt site j.isLt
    change i<N*(2^l*2^t*deg*2^(q+1))
    dsimp only [i];convert upper using 1; ring
  have end0 : f 42+f 43≤tail := by simp [fields,allocate,headerExtra,extraEnd]
  have bound : f 42+i<tail:=(Nat.add_lt_add_left hi _).trans_le end0
  have fit:=(bound.trans_le space.controls).trans cur.isLt
  apply (pub.child hi).read bound
  intro m frame
  let vs:=fun _ : Fin 1=>((f 42+i:ℕ):Word w)
  have h:=descriptor_field_frame space head frame
  have stored:=descriptor_input_frame space I frame
  have R:=stored.arc E vs code add sub
  rw [NodeRecipe.childrenBase,selected_word h vs]
  let ix:=(Owner.children P lay s).symm child
  have rank : Owner.indexOrder P lay s ix=j := (Owner.childOrder P lay s).symm_apply_apply j
  have childEq : Owner.child P lay s ix.val=child.val :=
    congrArg Subtype.val ((Owner.children P lay s).apply_symm_apply child)
  obtain ⟨⟨thin,slot,bb⟩,ok⟩:=ix
  rw [←childEq]
  apply ChildRows.entry_value S₀ P b E cur m vs R.toGraphReads code
    (field_word h vs 26 (by decide)) (field_word h vs 15 (by decide)) lay _ s thin slot bb ok c.node
    (field_word h vs 6 (by decide)) (field_nat h vs 15 (by decide)) (field_nat h vs 14 (by decide)) degree capFits bitsFit
  rw [offset_word h 42 i (by decide) fit,Fin.val_cast_of_lt (by omega),rank]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan

end OAI
