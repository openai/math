import OAI.Hierarchy.DescentParallelIncidentStream
import OAI.Hierarchy.DescentPackedOperandPublic
import OAI.Hierarchy.DescentSignedCableCodec

namespace OAI
/-! # Recover the actual next signed six-field record at each paid physical receiver slot -/
namespace Hierarchy.DescentNextSignedWindow
open DescentSharedCableNames DescentSIMDLookup DescentParallelBase DescentSixParty
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
variable {D cap : ℕ}

/-- One normalized raw parent, as seen at one of its actual signed ends.
A marked parent emits unit children; an unmarked tether has one child's
many grains and retains its single original source handle throughout. -/
structure Record (D cap : ℕ) where
  side : Bool
  neighbor : Fin D
  marked : Bool
  position : ℕ
  shared : ℕ
  atSource : ℕ
  count : ℕ

def number (cap : ℕ) (side : Bool) (i : ℕ):=side.toNat*cap+i

def render (r : Record D cap) (i : ℕ) : Option (Stage.Live D cap):=do
  let u:=r.shared+i
  let s:=r.atSource+(if r.marked then i else 0)
  let a:=if r.marked then 0 else i
  if ok : u<cap ∧ s<cap ∧ a<cap then return ⟨r.neighbor,⟨u,ok.1⟩,⟨s,ok.2.1⟩,⟨a,ok.2.2⟩,r.side,r.marked && !r.side⟩ else none

def read (r : Record D cap) (slot : Fin (2*cap)) : Option (Stage.Live D cap):=
  let begin:=number cap r.side r.position
  if begin≤ slot.val ∧ slot.val<begin+r.count then render r (slot.val-begin) else none

theorem indexed (r : Record D cap) (j : Fin r.count) (slot : Fin (2*cap)) (same : slot.val=number cap r.side r.position+j.val):
    read r slot=render r j.val :=by
  unfold read;rw [same,ite_eq_left (by have:=j.isLt;omega),Nat.add_sub_cancel_left]

theorem outside (r : Record D cap) (slot : Fin (2*cap)) (absent : ∀i:Fin r.count,slot.val≠number cap r.side r.position+i.val):read r slot=none:=by
  unfold read;rw [ite_eq_right];rintro ⟨lo,hi⟩;apply absent ⟨slot.val-number cap r.side r.position,by omega⟩
  exact (Nat.add_sub_of_le lo).symm

theorem «matches» (r : Record D cap) (j : Fin r.count) (truth : Stage.Live D cap) (peer:truth.neighbor=r.neighbor)
    (serial:truth.wire.val=r.shared+j.val) (origin:truth.sourceWire.val=r.atSource+(if r.marked then j.val else 0))
    (within:truth.within.val=(if r.marked then 0 else j.val)) (side:truth.target=r.side) (core:truth.markedOut=(r.marked && !r.side)):
    render r j.val=some truth:=by
  have good : r.shared+j.val<cap ∧ r.atSource+(if r.marked then j.val else 0)<cap ∧ (if r.marked then 0 else j.val)<cap:=
    ⟨serial ▸ truth.wire.isLt,origin ▸ truth.sourceWire.isLt,within ▸ truth.within.isLt⟩
  unfold render;rw [dite_eq_left good];congr 1;cases truth
  simp_all only [Stage.Live.mk.injEq,Fin.ext_iff,and_self]

/-- The executable physical lookup may sum the returned cell of every
prior raw parent, since at most one contains a given signed slot; empty
or out-of-group shelves contribute zero without overwriting a live row. -/
def collect {COUNT : ℕ} (rows : Fin COUNT→Option (Record D cap)) (slot : Fin (2*cap)) : Cell (DescentSignedCableCodec.width D cap) :=
  (∑i,(DescentSignedCableCodec.encode ((rows i).bind (fun raw=>read raw slot))).val:ℕ)

private theorem dead : DescentSignedCableCodec.encode (none:Option (Stage.Live D cap))=0 :=by apply Fin.ext;rfl

theorem collected {COUNT : ℕ} (rows : Fin COUNT→Option (Record D cap)) (slot : Fin (2*cap)) (wanted : Option (Stage.Live D cap))
    (empty : wanted=none→∀i,(rows i).bind (fun raw=>read raw slot)=none)
    (occupied : ∀q,wanted=some q→∃i,(rows i).bind (fun raw=>read raw slot)=some q ∧ ∀j,j≠i→(rows j).bind (fun raw=>read raw slot)=none) :
    collect rows slot=DescentSignedCableCodec.encode wanted:=by
  cases hit:wanted with
  | none=>rw [collect];simp [empty hit,dead]
  | some q=>
    obtain ⟨i,row,rest⟩:=occupied q hit
    unfold collect;rw [Fintype.sum_eq_single i (fun j neq=>by rw [rest j neq,dead];rfl),row];simp

section Stage
variable {F P V J : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
  (ready : A.StateBounds S i) (names : Stage.Host J V k↪ℕ)

/-- Exact criterion for a literal signed slot. `pos` is supplied by the
whole-incident streamed rank, including the child's offset. -/
theorem slot (h : Stage.Host J V k) (port : A.CellPorts h.1.1 h.1.2 h.2) (side : Bool) (pos : ℕ)
    (sign : (Stage.signedBit A h port).val=side.toNat) (index : ((Stage.source A native).position (Stage.measured A native S ready) h (Stage.ofPort A native h port)).val=pos) :
    (Stage.signed A native S ready h.1 h.2 port).val=number A.cap side pos:=by
  change (finProdFinEquiv (Stage.signedBit A h port,_)).val=_
  rw [finProdFinEquiv_apply_val,sign,index];unfold number;ring

theorem exact (h : Stage.Host J V k) (port : A.CellPorts h.1.1 h.1.2 h.2) (r : Record A.degree A.cap) (j : Fin r.count)
    (side : (Stage.signedBit A h port).val=r.side.toNat)
    (position : ((Stage.source A native).position (Stage.measured A native S ready) h (Stage.ofPort A native h port)).val=r.position+j.val)
    (physical : render r j.val=some (Stage.live A native S ready names h port)) :
    read r (Stage.signed A native S ready h.1 h.2 port)=Stage.signedPanel A native S ready names h (Stage.signed A native S ready h.1 h.2 port) :=by
  rw [Stage.signed_read,indexed r j _ (by rw [slot A native S ready h port r.side _ side position];unfold number;omega)];exact physical
end Stage
end
end Hierarchy.DescentNextSignedWindow

end OAI
