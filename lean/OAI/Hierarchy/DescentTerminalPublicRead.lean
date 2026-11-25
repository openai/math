import OAI.Hierarchy.DescentTerminalPublicGroup
import OAI.Hierarchy.DescentExteriorVerifiedRows

namespace OAI
/-! # Terminal exterior operands are bits of the actual phase-three RAM and public pins -/

namespace Hierarchy.DescentTerminalPublicRead
open DescentGL DescentColonies DescentInitialHost DescentSixParty Computability.BorderVNP.Crossing CorrectionFrame
open ThreeFlat Routing Catalyst CatalystSubstitution CorrectionBatch
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM
open DescentExterior DescentExteriorFetch ProtocolRAM DescentTerminalDenseWindow
open DescentTerminalGraphPositions DescentTerminalCableOrder DescentTerminalDenseGraphRead
open scoped Classical BigOperators Fin.CommRing
noncomputable section

set_option Elab.async false

variable {F : Type} [Field F] {arity data j r t bitsW : ℕ}
    (X : Approximation F arity data)

/- Each terminal bit names its true original occurrence and retained lane.
A genuine reset supplies these two fields by its portAddress and portOffset. -/
variable {P : Type} [Fintype P] {width : P→ℕ} {names : Fin (ExteriorCount X)→Type}
    (bitName : (z : P)→Fin (width z)→Σa : Fin (ExteriorCount X),names a × Fin t)
    (pre post : (a : Fin (ExteriorCount X))→names a→Bits (j+(j+r))) (history : ∀a : Fin (ExteriorCount X),DescentExterior.Record (pre a) (post a))
    (x : Catalyst.Port ((2^(j+(j+r))*t)*data) (copiesWidth (2^(j+(j+r))*t) X.width)→Bool)
    (z : Hidden (ExteriorCount X) j r t→Bool)

def original : Ports width := fun port b=>
  let nm := bitName port b
  packagePins X (2^(j+(j+r))) t x ⟨DescentColonies.address (j+(j+r)) (pre nm.1 nm.2.1),nm.1⟩ (finProdFinEquiv (nm.2.2,(0:Fin 1)))

def phaseRow (port : P) (b : Fin (width port)) : Fin ((ExteriorCount X)*2^(j+r)) :=
  let nm := bitName port b
  finProdFinEquiv (nm.1,rowOrd j r (coords j r (post nm.1 nm.2.1)).2)

def phaseBit (port : P) (b : Fin (width port)) : Fin (2^j*t) :=
  let nm := bitName port b
  pos j t ((coords j r (post nm.1 nm.2.1)).1,nm.2.2)

omit [Fintype P] [Field F] in
theorem resident (base : ℕ) (mem : Memory bitsW) (wordRoom : 2^j*t ≤ bitsW)
    (phases : ∀a : Fin (ExteriorCount X),stagesOK (j:=j) (r:=r) ((history a).layout) (publicRows (j:=j) (r:=r) (t:=t) X x a) (projected z false a) (projected z true a))
    (rows : ∀i : Fin ((ExteriorCount X)*2^(j+r)),mem (base+i.val)=((pack (fun l=>output ((history (slab i)).layout) (projected z true (slab i))
      (l,dest i))).val:Word bitsW)) (port : P) (b : Fin (width port)) :
    wordBits bitsW (mem (base+(phaseRow X bitName post port b).val))
      ((phaseBit X bitName post port b).castLE wordRoom)=original X bitName pre x port b := by
  let nm := bitName port b
  let a : Fin (ExteriorCount X) := nm.1
  let coord : Plane j r := coords j r (post a nm.2.1)
  let i : Fin ((ExteriorCount X)*2^(j+r)):=finProdFinEquiv (a,rowOrd j r coord.2)
  have outer : slab i=a ∧ dest i=coord.2 := by simp [slab,dest,i]
  let v:=pack (fun l=>output ((history a).layout) (projected z true a) (l,coord.2))
  have stored : mem (base+i.val)=(v.val:Word bitsW) := (rows i).trans <|
    congrArg₂ (fun (occ : Fin (ExteriorCount X)) (row : Rows j r) =>
      ((pack (fun l=>output (history occ).layout (projected z true occ) (l,row))).val : Word bitsW))
      outer.1 outer.2
  have limit:=v.isLt.trans_le (Nat.pow_le_pow_right (by decide) wordRoom)
  have widened : ∀l : Fin (2^j*t),wordBits bitsW ((v.val:ℕ):Word bitsW) (l.castLE wordRoom)=wordBits (2^j*t) v l := by
    intro l
    rw [←Computability.VPVNP.LiveHeader.testBit_wordBits,←Computability.VPVNP.LiveHeader.testBit_wordBits,Fin.val_cast_of_lt limit]; rfl
  change wordBits bitsW (mem (base+i.val)) ((pos j t (coord.1,nm.2.2)).castLE wordRoom)=_
  rw [stored,widened,pack_bit]
  change output ((history a).layout) (projected z true a) coord nm.2.2=_
  have same:=congrArg (coords j r) ((history a).read nm.2.1)
  rw [show coord=coords j r ((history a).layout (pre a nm.2.1)) from same]
  exact final_public_read X (fun a : Fin (ExteriorCount X)=>DescentExterior.Record.layout (history a)) x z phases a (pre a nm.2.1) nm.2.2

omit [Fintype P] [Field F] in
/-- Here the resident word premise comes directly from the actual finalMem
of the installed three-pass exterior procedure. -/
theorem native {start keyAt : ℕ} (kb : KeyBanks) (g : Fin 3→Banks) (guess : Fin 2→Bank)
    (ready : ∀s,(columns g guess s).Fits bitsW start) (m : Memory bitsW)
    (cap : ∀s,Capacity (g s) bitsW j r t (ExteriorCount X) start)
    (input : ∀s,Inputs (g s) s (fun a : Fin (ExteriorCount X)=>DescentExterior.Record.layout (history a)) (passInputs (publicRows (j:=j) (r:=r) (t:=t) X x) z s) (ProtocolRAM.image keyAt ((ExteriorCount X)*2^(j+r)) (joinKey kb) m))
    (wordRoom : 2^j*t ≤ bitsW)
    (phases : ∀a : Fin (ExteriorCount X),stagesOK (j:=j) (r:=r) ((history a).layout) (publicRows (j:=j) (r:=r) (t:=t) X x a) (projected z false a) (projected z true a))
    (port : P) (b : Fin (width port)) :
    wordBits bitsW ((finalMem keyAt start ((ExteriorCount X)*2^(j+r)) kb g guess m) (start+2*((ExteriorCount X)*2^(j+r))+(phaseRow X bitName post port b).val))
      ((phaseBit X bitName post port b).castLE wordRoom)=original X bitName pre x port b := by
  exact resident X bitName pre post history x z (start+2*((ExteriorCount X)*2^(j+r))) _ wordRoom phases
    (DescentExteriorFetch.final_row keyAt start kb g guess ready (fun a : Fin (ExteriorCount X)=>DescentExterior.Record.layout (history a)) (publicRows (j:=j) (r:=r) (t:=t) X x) z m cap input) port b

omit [Field F] in
/-- Each active exterior operand of the terminal graph is read in the
same genuine parent word as in the physical GL output; partial pieces
still vanish above their actual length. -/
theorem physical_slot {D S p q : ℕ} (N : Network D P width) (home : N.Site→Fin S)
    (nativeRank : N.Edge ↪ Fin (Fintype.card N.Edge)) (external : P ↪ ℕ)
    (nodes : N.Site ↪ ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
    (qp : 0<q*p) (orderOK : DescentTerminalPublicGroup.Clustered N home external)
    (base : ℕ) (mem : Memory bitsW) (wordRoom : 2^j*t ≤ bitsW)
    (phases : ∀a : Fin (ExteriorCount X),stagesOK (j:=j) (r:=r) ((history a).layout) (publicRows (j:=j) (r:=r) (t:=t) X x a) (projected z false a) (projected z true a))
    (rows : ∀i : Fin ((ExteriorCount X)*2^(j+r)),mem (base+i.val)=((pack (fun l=>output ((history (slab i)).layout) (projected z true (slab i))
      (l,dest i))).val:Word bitsW)) (i : Fin S)
    (gr : Order.Group (order N home nativeRank p external nodes ops) i) (exterior : gr.val=none)
    (row : ℕ) (s : Fin q) (port : P) (piece : Fin (poolBatchCount (width port) p))
    (hit : row*q+s.val<Fintype.card (Order.At (order N home nativeRank p external nodes ops) i gr))
    (label : ((Order.inGroup (order N home nativeRank p external nodes ops) i gr).symm ⟨_,hit⟩).val=.inr ⟨port,piece⟩)
    (bit : Fin p) :
    let L:=order N home nativeRank p external nodes ops
    let len:=groupLengths N L i gr
    let small : ∀a,len a ≤ p:=by intro a;unfold len groupLengths;cases ((Order.inGroup L i gr).symm a).val <;> exact Nat.min_le_left ..
    wordBits _ (fetched len qp small (DescentTerminalPublicGroup.siteBase N home i) row
      (publicStream external (original X bitName pre x))) (finProdFinEquiv (s,bit))=
      if active : piece.val*p+bit.val<width port then
        wordBits bitsW (mem (base+(phaseRow X bitName post port ⟨_,active⟩).val))
          ((phaseBit X bitName post port ⟨_,active⟩).castLE wordRoom) else false := by
  intro L len small
  rw [DescentTerminalPublicGroup.fetch_bit N home nativeRank external nodes ops qp orderOK
    (original X bitName pre x) i gr exterior row s port piece hit label bit]
  unfold TaggedShorterFields.slice
  split
  · exact (resident X bitName pre post history x z base mem wordRoom phases rows port _).symm
  · rfl

end
end Hierarchy.DescentTerminalPublicRead

end OAI
