import OAI.Hierarchy.DescentResetSignedHaloRight
import OAI.Hierarchy.DescentResetSignedHaloDate

namespace OAI
/-! # Read either end on the original donor board after the contact mass pass -/
namespace Hierarchy.DescentResetSignedHaloMatrix
open DescentSortedRoster DescentResetOriginHaloRAM DescentSIMDLookup DescentPackedZip DescentPackedColony DescentPackedChildNeighbor.SIMD
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable (C : Shelf) {w : ℕ}

theorem Shelf.stored {N : ℕ} (r : C.Fits w) (m : Memory w) (p : Fin C.oldHosts→Fin C.degree→Option (Fin C.oldHosts))
    (home : Fin N→Fin C.oldHosts) (bound : N≤C.hosts) (room : N≤C.owner.size) (digitRoom : C.degree+2<2^C.cargoBits)
    (counted : m C.oldCount.base=(N:Word w)) (homes : ∀i,m (C.owner.base+i.val)=((home i).val:Word w))
    (edges : ∀v j,m (C.oldRoster.base+(v.val*C.degree+j.val))=(target (p v j):Word w)) :
    Stored C.header C.hosts C.groups C.queryBits C.cargoBits C.lanes (short p home) (C.finalMem m):=by
  have early:=(C.extents r).2.1
  have measures_:=DescentResetSignedHaloMatrix.read r.old m p home bound room counted homes edges
  have words (h : Fin C.hosts) (j : Fin (C.degree+1)) : C.second m (C.ranks.base+(h.val*(C.degree+1)+j.val))=
      (((short (b:=C.cargoBits) p home h j).val):Word w):=by
    have ix:h.val*(C.degree+1)+j.val<C.hosts*(C.degree+1):=(Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)
    have pre := DescentOrdinaryAtomFieldRAM.ROM.frame C.pages (C.signedBits*C.lanes) C.decodeAt (C.first m)
      (C.ranks.base+(h.val*(C.degree+1)+j.val)) (.inl ((Nat.add_lt_add_left ix _).trans_le early))
    have digit : (short (b:=C.cargoBits) p home h j).val=rank p home h j :=
      Fin.val_cast_of_lt ((rank_bound p home h j).trans_lt digitRoom)
    rw [digit]
    exact pre.trans (measures_ h j)
  exact DescentPackedChildNeighbor.SIMD.ROM.stored C.ranks C.lookupAt _ _ (C.second m)
    (early.trans ((Nat.le_add_right ..).trans r.static_)) words

theorem Shelf.headerRoom (r : C.Fits w) :
    DescentPackedChildNeighbor.SIMD.Room C.header (.lit 0) C.hosts C.groups C.queryBits C.cargoBits C.lanes w C.high:=by
  have old : C.ranks.Fits w C.lookupAt:=⟨r.next.1,r.next.2.1,r.next.2.2.trans ((Nat.le_add_right ..).trans r.static_)⟩
  exact (DescentPackedChildNeighbor.SIMD.ROM.arranged_expr C.ranks (.lit 0) C.lookupAt ⟨old,r.length⟩ trivial r.enough).2

private theorem stored_below {T H G a b M cut w : ℕ} {L : DescentPackedChildNeighbor.SIMD.Chart T}
    (r : DescentPackedChildNeighbor.SIMD.Room L (.lit 0) H G a b M w cut)
    {val : Fin H→Fin T→Cell b} {m o : Memory w} (data_ : Stored L H G a b M val m)
    (same : ∀z,z<cut→ o z=m z) : Stored L H G a b M val o:=by
  have ordinary (B : Bank) (fit : B.Fits w cut) {i : ℕ} (inside : i<B.size) :
      o (B.base+i)=m (B.base+i):=same _ ((Nat.add_lt_add_left inside _).trans_le fit.2.2)
  constructor
  · intro v j
    have ix:v.val*T+j.val<H*T:=(Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
    exact (ordinary _ r.tableFits (ix.trans_le r.headers)).trans (data_.values v j)
  · intro p
    exact (ordinary _ r.offFits ((row H G M p).isLt.trans_le r.rows)).trans (data_.offsets p)
  · intro i
    exact (ordinary _ r.shiftFits (by simp [Bank.size,r.shifts])).trans (data_.shifts i)
  · intro j i
    exact (ordinary _ (r.pageFits j) (by simp [Bank.size,r.pages])).trans (data_.pages j i)
  · exact ⟨fun i=>(ordinary _ r.joinShift (by simp [Bank.size,r.joinLeft])).trans (data_.joins.1 i),
      fun i=>(ordinary _ r.joinApply (by simp [Bank.size,r.joinBoth])).trans (data_.joins.2 i)⟩

namespace Right
def pages:=DescentOrdinaryAtomFieldRAM.ROM.binary (askedField C.degree C.cap C.signedBits C.queryBits) C.lanes
def high (root : ℕ):=root+C.delta
def program (root w : ℕ):=DescentOrdinaryAtomFieldRAM.ROM.mount (pages C) (C.signedBits*C.lanes) w root
def memory (root : ℕ) (m : Memory w):=DescentOrdinaryAtomFieldRAM.ROM.after (pages C) (C.signedBits*C.lanes) root m
def ticks:=4+10*C.delta
def port (root : ℕ) (src : Expr):=body C.header (query C.degree C.cap C.signedBits C.queryBits C.lanes root src) (List.finRange (C.degree+1))

theorem any (root : ℕ) (room : high C root<2^w) (m : Memory w) :
    (program C root w).Exec m (memory C root m) (ticks C) ∧ CheapCode (program C root w) ∧
    ∀z,z<root ∨ high C root≤z→memory C root m z=m z:=by
  exact ⟨(DescentOrdinaryAtomFieldRAM.ROM.run (pages C) _ root m room).1,DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _,
    DescentOrdinaryAtomFieldRAM.ROM.frame (pages C) _ root m⟩

/-- Published old matrix plus installed address and lookup tables are reused verbatim. -/
theorem posted (root : ℕ) (r : C.Fits w) (below : C.high≤root)
    (room : high C root+C.hosts*chunks C.groups C.lanes<2^w) {old m : Memory w}
    (val : Fin C.hosts→Fin (C.degree+1)→Cell C.cargoBits)
    (archive : Stored C.header C.hosts C.groups C.queryBits C.cargoBits C.lanes val old)
    (held : ∀z,z<C.high→m z=old z) (src : Expr) (x : Fin C.hosts→Fin C.groups→Cell C.signedBits)
    (fit : src.Fits w root) (signed : Source src x C.lanes m) :
    (port C root src).Fits w (high C root) ∧ Source (port C root src)
      (fun h g=>lookup (val h) (askedField C.degree C.cap C.signedBits C.queryBits (x h g) 0) (List.finRange (C.degree+1)))
      C.lanes (memory C root m):=by
  have space : high C root<2^w:=(Nat.le_add_right ..).trans_lt room
  have installed:=decoder_run (H:=C.hosts) (G:=C.groups) (M:=C.lanes) C.degree C.cap C.signedBits C.queryBits root m space
  have mark:=installed.2.1 src x fit signed
  have prev:=C.headerRoom r
  have saved:=stored_below prev archive (m:=old) (o:=memory C root m)
    (fun z l=>(installed.2.2.1 z (.inl (l.trans_le below))).trans (held z l))
  have bound : C.high≤high C root:=below.trans (Nat.le_add_right ..)
  have move {B : Bank} (f : B.Fits w C.high) : B.Fits w (high C root):=⟨f.1,f.2.1,f.2.2.trans bound⟩
  let q:=query C.degree C.cap C.signedBits C.queryBits C.lanes root src
  have safe : DescentPackedChildNeighbor.SIMD.Room C.header q C.hosts C.groups C.queryBits C.cargoBits C.lanes w (high C root):=
    ⟨mark.1,move prev.tableFits,move prev.offFits,move prev.shiftFits,fun j=>move (prev.pageFits j),
      move prev.joinShift,move prev.joinApply,prev.headers,prev.rows,prev.shifts,prev.pages,prev.joinLeft,prev.joinBoth,room⟩
  exact ⟨fitted _ _ safe _,measures _ _ _ safe _ _ saved _ mark.2 _⟩

end Right
end
end Hierarchy.DescentResetSignedHaloMatrix

end OAI
