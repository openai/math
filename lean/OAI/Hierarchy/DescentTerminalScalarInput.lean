import OAI.Hierarchy.DescentTerminalBundleRows
import OAI.Hierarchy.DescentTerminalDenseCableFetch
import OAI.Hierarchy.DescentTerminalPublicGroup
import OAI.Hierarchy.DescentTerminalDenseWindowRAM
import OAI.Hierarchy.DescentTerminalScalarTransposes

namespace OAI
/-! # The reached two-word source for every real terminal scalar operand -/
namespace Hierarchy.DescentTerminalScalarInput
open DescentKernelHistory (Recipe Boundary)
open DescentTerminalGraphPositions DescentTerminalCableOrder
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow DescentTerminalRecipeRows
open DescentTerminalBundleRows DescentTerminalScalarTransposes
open ThreeFlat.Routing ThreeFlat.RAM
open Computability.VPVNP.RAMSerialization Computability.VPVNP.BurstRAM PrivateRAM
open Computability.BorderVNP.Crossing DescentTerminalPorts
open scoped BigOperators Classical
noncomputable section

variable {Tag P : Type} [Fintype P] {S D p q W piece rawRows bitsW : ℕ} {ew : P→ℕ}
    (N : Network D P ew) (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ)
local notation "L" => order N home native p external nodes ops
variable (r : ∀v,Recipe Tag (SiteRef (p:=p) N v)) (hp : 0<p) (birth : ∀v,(r v).Node ↪ ℕ)
    (wp : 0<W) (qp : 0<q)
local notation "sites" => DescentTerminalBundleRows.site L r hp birth
local notation "count" => Bins (W:=W) (q:=q) sites
local notation "pos" => Nat.mul_pos qp hp

def physical (z : Named sites) : Fin (count*W) :=
  let a:=source sites wp qp z
  finProdFinEquiv (a.1,a.2.1)

variable (pay : RowBit rawRows (q*p)→Bool) (outer : Ports ew)
def raw (j : ℕ) : Word (q*p) :=
  if j<rawRows+2 then dense (q*p) (stream pay) j
  else dense (q*p) (publicStream external outer) (j-(rawRows+2))

def group {i : Fin S} (z : (sites i).Name) : Order.Group L i := ((Order.groups L i).symm z.1)
def localRow {i : Fin S} (z : (sites i).Name) := z.2.val/q
def column {i : Fin S} (z : (sites i).Name) : Fin q := ⟨z.2.val%q,Nat.mod_lt _ qp⟩
def lengths {i : Fin S} (z : (sites i).Name) := groupLengths N L i (group N home native external nodes ops r hp birth z)
theorem short {i : Fin S} (z : (sites i).Name) : ∀u,lengths N home native external nodes ops r hp birth z u ≤ p := by
  intro u
  unfold lengths groupLengths
  cases ((Order.inGroup L i _).symm u).val <;> exact Nat.min_le_left ..
def base {i : Fin S} (z : (sites i).Name) :=
  (group N home native external nodes ops r hp birth z).val.elim
    (DescentTerminalPublicGroup.siteBase N home i) (pairBase N home i)
def bankOffset {i : Fin S} (z : (sites i).Name) (rawCount : ℕ) :=
  if (group N home native external nodes ops r hp birth z).val.isSome then 0 else rawCount+2

def index (z : Named sites) : ℕ := bankOffset N home native external nodes ops r hp birth z.2 rawRows+
  first (lengths N home native external nodes ops r hp birth z.2) q (base N home native external nodes ops r hp birth z.2)
    (localRow (q:=q) N home native external nodes ops r hp birth z.2)/(q*p)
def control (z : Named sites) := format (lengths N home native external nodes ops r hp birth z.2) pos
  (short N home native external nodes ops r hp birth z.2) (base N home native external nodes ops r hp birth z.2)
  (localRow (q:=q) N home native external nodes ops r hp birth z.2)

theorem group_read (room : (∑e,N.width e) ≤ rawRows*(q*p))
    (ordered : DescentTerminalPublicGroup.Clustered N home external) (z : Named sites) (j : Fin p) :
    let idx:=index (q:=q) (rawRows:=rawRows) N home native external nodes ops r hp birth z
    let fmt:=control N home native external nodes ops r hp birth qp z
    wordBits _ (word fmt (raw external pay outer idx) (raw external pay outer (idx+1)))
      (finProdFinEquiv (column N home native external nodes ops r hp birth qp z.2,j))=
      Order.readName (N:=N) (takeBits N (denseBits N (edgeCode N home native) room) pay) outer ((L).catalog z.1 z.2) j := by
  intro idx fmt
  let g:=group N home native external nodes ops r hp birth z.2
  let s:=column N home native external nodes ops r hp birth qp z.2
  let row:=localRow (q:=q) N home native external nodes ops r hp birth z.2
  have eqn : row*q+s.val=z.2.2.val := Nat.div_add_mod' z.2.2.val q
  have hit : row*q+s.val<Fintype.card (Order.At L z.1 g) := by rw [eqn]; exact z.2.2.isLt
  let name:=((Order.inGroup L z.1 g).symm (⟨_,hit⟩:Fin _))
  have columnEq : (⟨row*q+s.val,hit⟩ : Fin (Fintype.card (Order.At L z.1 g)))=z.2.2 := Fin.ext eqn
  have same : name.val=(L).catalog z.1 z.2 :=
    congrArg (fun a=>((Order.inGroup L z.1 g).symm a).val) columnEq
  have grp : group N home native external nodes ops r hp birth z.2=g := rfl
  have kind := name.property.2
  cases label : name.val with
  | inl cable=>
    obtain ⟨e,k⟩:=cable
    let h:=if home (N.src e)=z.1 then home (N.dst e) else home (N.src e)
    have interior : g.val=some h := kind.symm.trans (congrArg (Order.neighbor L z.1) label)
    have rowIn : row<poolBatchCount (Fintype.card (Order.At L z.1 g)) q := by
      have cover:=CallPool.count_le_batches_mul (Fintype.card (Order.At L z.1 g)) q qp
      exact (Nat.div_lt_iff_lt_mul qp).mpr (z.2.2.isLt.trans_le (cover.trans_eq (Nat.mul_comm ..)))
    let packet : DescentTerminalDenseCableFetch.Packet N L q:=⟨z.1,h,g,interior,⟨row,rowIn⟩⟩
    let first:=DescentTerminalDenseCableFetch.index N home native external nodes ops packet
    have sentinel : first+1<rawRows+2:=DescentTerminalDenseCableFetch.index_sentinel N home native external nodes ops pos room packet
    have idxEq : idx=first := by
      simp [idx,index,bankOffset,base,grp,interior,first,packet,DescentTerminalDenseCableFetch.index,row,lengths]; rfl
    have fmtEq : fmt=DescentTerminalDenseCableFetch.fmt N home native external nodes ops pos packet := by
      simp [fmt,control,base,grp,interior,DescentTerminalDenseCableFetch.fmt,lengths,packet,row]; rfl
    rw [←same,label,idxEq,fmtEq,raw,ite_eq_left (by omega),raw,ite_eq_left sentinel]
    exact DescentTerminalDenseCableFetch.fetch_bit N home native external nodes ops pos room pay packet s e k hit label j
  | inr pin=>
    obtain ⟨u,k⟩:=pin
    have exterior : g.val=none := kind.symm.trans (congrArg (Order.neighbor L z.1) label)
    let len:=groupLengths N L z.1 g
    let start:=first len q (DescentTerminalPublicGroup.siteBase N home z.1) row/(q*p)
    have idxEq : idx=rawRows+2+start := by
      simp [idx,index,bankOffset,base,grp,exterior,len,start,lengths,row]; rfl
    rw [←same,label,idxEq]
    have hi : rawRows+2+start-(rawRows+2)=start := Nat.add_sub_cancel_left _ _
    have hi' : rawRows+2+start+1-(rawRows+2)=start+1 := by
      rw [Nat.add_assoc (rawRows+2) start 1, Nat.add_sub_cancel_left]
    simp only [raw,ite_eq_right (by omega : ¬rawRows+2+start<rawRows+2),ite_eq_right (by omega : ¬rawRows+2+start+1<rawRows+2),hi,hi']
    have read := DescentTerminalPublicGroup.fetch_bit N home native external nodes ops pos ordered outer z.1 g exterior row s u k hit label j
    simp [fetched,fmt,control,base,grp,exterior,len,start,lengths,row] at read ⊢
    simpa only [g,s,Order.readName] using read

/-- Physical header inputs only: the reached port-row pointer identifies the
two earlier rows, and the format names the clipped pieces of that group.
Padding and table rows may carry any legal lookup, since no physical
source operand names any of their slots. -/
structure Headers (idx : Fin (count*W)→ℕ) (fmt : Fin (count*W)→Format q p) : Prop where
  indexAt : ∀z,idx (physical N home native external nodes ops r hp birth wp qp z)=
    index (q:=q) (rawRows:=rawRows) N home native external nodes ops r hp birth z
  formatAt : ∀z,fmt (physical N home native external nodes ops r hp birth wp qp z)=
    control N home native external nodes ops r hp birth qp z

theorem observed (payloadWidth : p=W*piece) (room : (∑e,N.width e) ≤ rawRows*(q*p))
    (ordered : DescentTerminalPublicGroup.Clustered N home external) (wordRoom : q*p ≤ bitsW)
    (idx : Fin (count*W)→ℕ) (fmt : Fin (count*W)→Format q p)
    (header : Headers (rawRows:=rawRows) N home native external nodes ops r hp birth wp qp idx fmt)
    (m : Memory bitsW) (out : ℕ) (X : Proposal count W q piece)
    (checked : ∀i, rowWord X i=(low (payloadWidth ▸ wordRoom)
      (fillSegment out (count*W) (DescentTerminalDenseWindowRAM.file out idx fmt (raw external pay outer)) m (out+i.val)))) :
    ∀(z : Named sites) (d : Fin (W*piece)),let t:=source sites wp qp z
      X t.1 t.2 d=DescentTerminalBundleRows.payload L r hp birth wp qp payloadWidth
        (takeBits N (denseBits N (edgeCode N home native) room) pay) outer t.1 t.2 d := by
  subst p
  intro z d t
  let i:=physical N home native external nodes ops r hp birth wp qp z
  let j:=finProdFinEquiv (t.2.2,d)
  have bit:=congrArg (fun v=>wordBits _ v j) (checked i)
  simp only [rowWord,physical,i,Equiv.symm_apply_apply,Equiv.apply_symm_apply,low,j] at bit
  have emitted:=DescentTerminalDenseWindowRAM.output_bit out idx fmt (raw external pay outer) m i j wordRoom
  have atIndex : idx i=_ := header.indexAt z
  have atFormat : fmt i=_ := header.formatAt z
  rw [atIndex,atFormat] at emitted
  have named:=group_read N home native external nodes ops r hp birth qp pay outer room ordered z d
  have payloadAt:=DescentTerminalBundleRows.payload_source (order N home native (W*piece) external nodes ops)
    r hp birth wp qp rfl (takeBits N (denseBits N (edgeCode N home native) room) pay) outer z d
  exact bit.trans (emitted.trans (named.trans payloadAt.symm))

end
end Hierarchy.DescentTerminalScalarInput

end OAI
