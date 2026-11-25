import OAI.ThreeFlat.Diagonal.CompressorSuccessorFiles

namespace OAI
/-! # Physical values of the installed three file writers under their actual resident input -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.PhysicalPinsExpr Placement Graph
open scoped Classical Fin.NatCast
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l pad : ℕ}
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors) (b : B ≃ Fin N)
variable (bound : ∀i,S.pieces i≤S.pieceRadix) (lay : Bool) (hc : 2≤S.colors)
variable (good : TagConditions P.slots (shift P) P.offset) (ht : 0<t)
variable (E : Codec B w S.colors t l)
variable (prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ) (supply : P.Motif → Fin 8 → ℕ)
variable (p : Pointers) (cell : Word w)

structure Fits : Prop where
  code : ∀v,E.base v=((b v).val:Word w)
  inj : Function.Injective E.base
  slotAdd : ∀ u v,slotCode (w:=w) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v)
  slotSub : ∀ u v,slotCode (w:=w) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v)
  keys : ∀e,edgeId S P (baseNat b) bound e<2^w
  supplied : ∀ m j,supply m j<2^w
  bases : ∀v : B × BitWord t,(E.base v.1).val*2^t+(tagOrdinal t v.2).val<2^w
  degree : S.outputDegree=(liveDegree S + pad)
  live : S.liveDegree=liveDegree S
  boundDegree : (liveDegree S + pad)<2^w
  radix : S.pieceRadix<2^w ∧ 4<2^w ∧ S.degree<2^w ∧ 2^S.colors<2^w ∧ 2^t<2^w
  lanes : 2^l<2^w
  six : 6≤2^w

variable {S P b bound lay hc good ht E prior supply p cell}
variable (h : Fits (pad:=pad) S P b bound E supply)
variable (z : Separation (w:=w) (dims S N t l) p cell.val) {m : Memory w}
variable (I : Input S P b hc lay p cell prior supply m)

include h in
omit [Fintype B] [Fintype H] in
theorem Fits.one : (1:Word w)≠0 := by
  have lone : 1<2^w := by have := h.six; omega
  have cast := Fin.val_cast_of_lt (n:=2^w) lone
  intro e
  have q:=congrArg Fin.val e
  have v : (1:Word w).val=1 := by simpa using cast
  rw [v,Fin.val_zero] at q
  omega

include I in
omit [Fintype B] [Fintype H] in
theorem Input.chosen (vs : Fin 1 → Word w) :
    Formula.value (fun _=>cell) m vs (Template.f selected)=if lay then 1 else 0 := by
  have h := I.hdr.field vs (27:Fin 34)
  cases lay <;> exact h

include h z I in
theorem graph_row (good : TagConditions P.slots (shift P) P.offset) (ht : 0<t) (pub : Fin 1→Word w)
    (u : (Bool × Fin 3) × ((B × BitWord t) × Fin (liveDegree S + pad))) :
    (Template.emit cell (Template.graph S false)).eval pub m
      (fun _=>(((outgoing S N t p).graph+(PostImage.graphNumbers (Template.tagNumber (t:=t) b) u).val:ℕ):Word w)) =
        (SlotImage.fields (successor (pad:=pad) S P b bound lay hc good ht) (Template.tagNumber (t:=t) b) (tagOrdinal l) u.2 u.1.1 u.1.2:Word w) := by
  let vs:=fun _ : Fin 1=>(((outgoing S N t p).graph+(PostImage.graphNumbers (Template.tagNumber (t:=t) b) u).val:ℕ):Word w)
  have rows : (outgoing S N t p).rows=N*2^t*(liveDegree S + pad) := congrArg (fun a=>N*2^t*a) h.degree
  rw [Template.program_value]
  apply Template.physical_graph_read cell pub m vs S P b E (I.arc E vs h.code h.slotAdd h.slotSub)
    h.code h.inj bound h.keys lay hc good ht (I.hdr.radices vs) h.live h.degree (I.chosen vs) h.one
    h.six h.boundDegree h.radix.2.2.2.2 h.bases (outgoing S N t p) rows z.graphEnd
    (I.hdr.field vs 20) (I.hdr.field vs 22) u.2 u.1.1 u.1.2
  rw [←PostImage.graphNumbers_val (Template.tagNumber (t:=t) b) u.2 u.1.1 u.1.2 (outgoing S N t p) rows]

include h z I in
theorem key_row (good : TagConditions P.slots (shift P) P.offset) (pub : Fin 1→Word w)
    (u : (B × BitWord t) × Fin (liveDegree S + pad)) :
    (Template.emit cell (Template.graph S true)).eval pub m
      (fun _=>((p.keys+(PostImage.slotNumbers (Template.tagNumber (t:=t) b) u).val:ℕ):Word w)) =
        (Template.sourceKey S P b bound lay hc u:Word w) := by
  let vs:=fun _ : Fin 1=>((p.keys+(PostImage.slotNumbers (Template.tagNumber (t:=t) b) u).val:ℕ):Word w)
  rw [Template.program_value]
  have safe : N*2^t*S.outputDegree<2^w := by
    have keyEnd : p.keys + N*2^t*S.outputDegree < 2^w := z.keyEnd
    omega
  apply Template.physical_key_read S P b bound lay hc cell pub m vs E (I.arc E vs h.code h.slotAdd h.slotSub)
    h.code h.inj h.keys good (I.hdr.radices vs) h.live h.degree (I.chosen vs) h.one h.boundDegree
    h.radix.2.2.2.2 h.bases p.keys (by simpa only [←h.degree] using safe) (I.hdr.field vs 23) u
  dsimp only [vs]
  rw [PostImage.slotNumbers_val]

include h z I in
theorem width_row (good : TagConditions P.slots (shift P) P.offset) (pub : Fin 1→Word w)
    (e : SlotImage.Edge (B × BitWord t) (BitWord l) (liveDegree S + pad))
    (key : m (p.keys+SlotImage.ordinal (Template.tagNumber (t:=t) b) e.1)=(Template.sourceKey S P b bound lay hc e.1:Word w)) :
    (Template.emit cell (Template.output S)).eval pub m
      (fun _=>(((outgoing S N t p).widths+(PostImage.edgeNumbers (Template.tagNumber (t:=t) b) (tagOrdinal l) e).val:ℕ):Word w))=(newWidth (pad:=pad) S P b bound lay hc good supply e:Word w) := by
  let vs:=fun _ : Fin 1=>(((outgoing S N t p).widths+(PostImage.edgeNumbers (Template.tagNumber (t:=t) b) (tagOrdinal l) e).val:ℕ):Word w)
  have keyLimit:=z.keyEnd
  have widthLimit:=z.safe
  have ordinal : SlotImage.ordinal (Template.tagNumber (t:=t) b) e.1<(dims S N t l).newEdges := by
    rw [show (dims S N t l).newEdges=(N*2^t)*(liveDegree S + pad) from congrArg (fun a=>N*2^t*a) h.degree]
    exact SlotImage.ordinal_lt (Template.tagNumber (t:=t) b) e.1
  have idx : SlotImage.edgeOrdinal (Template.tagNumber (t:=t) b) (tagOrdinal l) e<(dims S N t l).newEdges*2^l := by
    rw [show (dims S N t l).newEdges=(N*2^t)*(liveDegree S + pad) from congrArg (fun a=>N*2^t*a) h.degree]
    exact SlotImage.edgeOrdinal_lt (Template.tagNumber (t:=t) b) (tagOrdinal l) e
  rw [Template.program_value]
  apply Template.physical_width_read cell m vs S P b bound lay hc good E
    (I.arc E vs h.code h.slotAdd h.slotSub) prior (I.widths E vs h.code) supply (I.chosen vs)
    h.one h.radix h.keys h.supplied p.newWidths p.keys (I.hdr.field vs 24) (I.hdr.field vs 23)
    (I.hdr.field vs 14) h.lanes (I.supply vs) e.1 e.2 (by omega) ?_ ?_ key
  · exact (Nat.add_lt_add_left idx _).trans widthLimit
  · dsimp only [vs]
    rw [PostImage.edgeNumbers_val]
    rfl


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
