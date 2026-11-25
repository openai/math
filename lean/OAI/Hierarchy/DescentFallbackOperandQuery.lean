import OAI.Hierarchy.DescentOperandFamilyBook
import OAI.Hierarchy.DescentPrivateTreeGeometry
import OAI.Hierarchy.DescentResetLocalRoster

namespace OAI
/-! # Directed reset operand addresses from measured tree paths and public socket fields -/

namespace Hierarchy.DescentFallbackOperandQuery
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentResetLocalRoster
open DescentTreePrefixIntervals DescentPrivateTreeTemplate DescentHostDirectory
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section

/-- The word sent by a tree item is its leaf address, independent of the level at which the
    equality gate reads that item.  The dictionary contains only the finite public tree. -/
def pathRank (h d leaf : ℕ) : ℕ :=
  if hd : d<h then
    if contains : ∃t : Bits h,lex h t=leaf then
      (order h ⟨⟨d,hd⟩,cut (by omega : d+1≤h) contains.choose⟩).val
    else 0
  else 0

theorem pathRank_read {h : ℕ} (d : Fin h) (t : Bits h) :
    pathRank h d.val (lex h t) =
      (order h ⟨d,cut (by omega : d.val+1≤h) t⟩).val := by
  have hit : ∃u : Bits h,lex h u=lex h t:=⟨t,rfl⟩
  rw [pathRank,dite_eq_left d.isLt,dite_eq_left hit,(lex_injective h hit.choose_spec)]

/-- A zero root tag is good.  A positive tag stores one plus the option row of an
    exceptional terminal.  The dyadic label is reconstructed from its two measured digits. -/
def rootNumber (r Y d off tag : ℕ) : ℕ :=
  if ok : (d,off)∈codes r then
    let slot:=(DescentResetCableSlots.interval r ⟨(d,off),ok⟩).val
    if tag=0 then slot else 2^(r+1)+slot*(Y+1)+(tag-1)
  else 0

theorem good_root {r Y : ℕ} (c : code r) :
    rootNumber r Y c.val.1 c.val.2 0=(rootId r Y (.inl c)).val := by
  rcases c with ⟨⟨d,off⟩,ok⟩
  calc
    _ = (DescentResetCableSlots.interval r ⟨(d,off),ok⟩).val := by simp [rootNumber,ok]
    _ = _ := rfl

theorem fallback_root {r Y : ℕ} (c : code r) (o : Option (Fin Y)) :
    rootNumber r Y c.val.1 c.val.2 ((DescentResetWireTags.optionRow o)+1)=
      (rootId r Y (.inr (c,o))).val := by
  rcases c with ⟨⟨d,off⟩,ok⟩
  let slot := (DescentResetCableSlots.interval r ⟨(d,off),ok⟩).val
  let row := DescentResetWireTags.optionRow o
  calc
    _ = 2^(r+1) + slot*(Y+1) + row := by simp [rootNumber,ok,slot,row]
    _ = 2^(r+1) + (row + (Y+1)*slot) := by ac_rfl
    _ = _ := rfl

inductive Operand where
  | stem (oldSide : Bool)
  | contact (face : Bool)
  | tree (side face : Bool) (height level : ℕ)
deriving DecidableEq

structure Shape where
  residual : ℕ
  sectors : ℕ
  maxDepth : ℕ
  privateSlots : ℕ
  fieldBits : ℕ
  queryBits : ℕ
  lanes : ℕ

def stemSlots (C : Shape) (cap : ℕ) :=2*(2^C.residual*(2*cap))
def sockets (C : Shape) :=C.sectors+2^C.maxDepth
def contactSlots (C : Shape) :=2*(rootSlots C.residual C.sectors * sockets C)
def total (C : Shape) (cap : ℕ) :=
  stemSlots C cap+(1+(contactSlots C+2*(rootSlots C.residual C.sectors*C.privateSlots)))
def directed (K : ℕ) (face : Bool) (position : ℕ) :=(if face then K else 0)+position+1

/-- Registers 0 and 1 contain occupancy and old cap.  For stems the next two
    registers contain the prior residual group and signed slot.  For bank gates they
    contain terminal depth and offset, followed by the terminal tag, the old leaf or
    socket, and the canonical contact owner side. -/
def number (C : Shape) (op : Operand) (x : Fin 7→Cell C.fieldBits) : ℕ :=
  let cap:=(x 1).val
  let root:=rootNumber C.residual C.sectors (x 2).val (x 3).val (x 4).val
  let roots:=rootSlots C.residual C.sectors
  if (x 0).val=0 then 0 else
    match op with
    | .stem s =>
      directed (total C cap) true
        ((finTwoEquiv.symm s).val*(2^C.residual*(2*cap))+(x 2).val*(2*cap)+(x 3).val)
    | .contact face =>
      let owner:=(x 6).val%2
      directed (total C cap) face (stemSlots C cap+1+
        (owner*(roots*sockets C)+root*sockets C+(x 5).val))
    | .tree s face h d =>
      directed (total C cap) face (stemSlots C cap+1+contactSlots C+
        ((finTwoEquiv.symm s).val*(roots*C.privateSlots)+root*C.privateSlots+pathRank h d (x 5).val))

structure Book (Q : ℕ) extends Shape where
  operand : Fin Q→Operand

namespace Book
variable {Q : ℕ} (B : Book Q)
def law (j : Fin Q) (x : Fin 7→Cell B.fieldBits) : Cell B.queryBits :=
  number B.toShape (B.operand j) x

theorem empty (j : Fin Q) : B.law j (fun _=>0)=0 := by simp [law,number]

abbrev program (base w : ℕ) := DescentOperandFamilyBook.program B.law B.lanes base w
abbrev image {w : ℕ} (base : ℕ) (m : Memory w) := DescentOperandFamilyBook.image B.law B.lanes base m
abbrev ticks :=DescentOperandFamilyBook.ticks Q 7 B.fieldBits B.lanes
abbrev endAddress (base : ℕ) :=DescentOperandFamilyBook.endAddress Q 7 B.fieldBits B.lanes base
abbrev expr (base : ℕ) (j : Fin Q) (src : Fin 7→Expr) :=DescentOperandFamilyBook.expr B.law B.lanes base j src
abbrev any {w : ℕ} (base : ℕ) (m : Memory w) (room : B.endAddress base<2^w) :=
  DescentOperandFamilyBook.any B.law B.lanes base m room
abbrev issued {H G w : ℕ} (base : ℕ) (j : Fin Q) (src : Fin 7→Expr) (m : Memory w)
    (x : Fin H→Fin G→Fin 7→Cell B.fieldBits) (bounds : ∀i,(src i).Fits w base)
    (reads : ∀i,DescentPackedZip.Source (src i) (fun v g=>x v g i) B.lanes m) (room : B.endAddress base<2^w) :=
  DescentOperandFamilyBook.issued B.law B.empty B.lanes base j src m x bounds reads room
abbrev expr_work (base : ℕ) (j : Fin Q) (src : Fin 7→Expr) (t : ℕ) (price : ∀i,(src i).work≤t) :=
  DescentOperandFamilyBook.expr_work B.law B.lanes base j src t price
end Book

end
end Hierarchy.DescentFallbackOperandQuery

end OAI
