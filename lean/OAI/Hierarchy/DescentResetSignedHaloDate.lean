import OAI.Hierarchy.DescentResetSignedHaloPacked
import OAI.Hierarchy.DescentResetSignedHaloDecoder
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # One clocked source of the earlier source-halo cargo of all signed ports -/
namespace Hierarchy.DescentResetSignedHaloMatrix
open DescentPackedColony DescentSIMDLookup DescentSortedRoster DescentPackedZip DescentSixParty.Chronology DescentResetOriginHaloRAM
open DescentPackedChildNeighbor.SIMD DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
structure Shelf where
  oldCount : Bank
  oldRoster : Bank
  owner : Bank
  ranks : Bank
  root : ℕ
  decodeAt : ℕ
  lookupAt : ℕ
  hosts : ℕ
  oldHosts : ℕ
  degree : ℕ
  cap : ℕ
  groups : ℕ
  lanes : ℕ
  signedBits : ℕ
  queryBits : ℕ
  cargoBits : ℕ

namespace Shelf
variable (C : Shelf) {w : ℕ}
def delta:=2*2^(C.signedBits*C.lanes)
def pages:=binary (askedField C.degree C.cap C.signedBits C.queryBits) C.lanes
def count:=DescentPackedChildNeighbor.SIMD.ROM.cells (C.degree+1) C.queryBits C.cargoBits C.lanes C.hosts C.groups
def high:=DescentPackedChildNeighbor.SIMD.ROM.output C.lookupAt (C.degree+1) C.queryBits C.cargoBits C.lanes C.hosts C.groups
def header:=DescentPackedChildNeighbor.SIMD.ROM.layout C.lookupAt (C.degree+1) C.queryBits C.cargoBits C.lanes (DescentPackedChildNeighbor.SIMD.ROM.rowBits C.hosts C.groups C.lanes) C.ranks
def port (signed : Expr):=body C.header (query C.degree C.cap C.signedBits C.queryBits C.lanes C.decodeAt signed) (List.finRange (C.degree+1))
def first (m : Memory w):=dst C.hosts C.degree C.oldHosts C.root C.ranks.base C.oldCount C.owner C.oldRoster m
def second (m : Memory w):=DescentOrdinaryAtomFieldRAM.ROM.after C.pages (C.signedBits*C.lanes) C.decodeAt (C.first m)
def finalMem (m : Memory w):=DescentPackedChildNeighbor.SIMD.ROM.after C.lookupAt (C.degree+1) C.queryBits C.cargoBits C.lanes C.hosts C.groups (C.second m)
def cpu (w : ℕ):=((program C.hosts C.degree C.oldHosts w C.root C.ranks.base C.oldCount C.owner C.oldRoster).seq
  (mount C.pages (C.signedBits*C.lanes) w C.decodeAt)).seq (DescentPackedChildNeighbor.SIMD.ROM.program C.lookupAt (C.degree+1) C.queryBits C.cargoBits C.lanes C.hosts C.groups w)
def ticks:=clock C.hosts C.degree C.oldHosts C.root C.oldCount C.owner C.oldRoster+(4+10*C.delta)+(4+10*C.count)
structure Fits (w : ℕ) : Prop where
  old : Room C.hosts C.degree C.oldHosts w C.root C.ranks.base C.oldCount C.owner C.oldRoster
  next : C.ranks.Fits w C.decodeAt
  length : C.hosts*(C.degree+1)≤C.ranks.size
  static_ : C.decodeAt+C.delta≤C.lookupAt
  enough : C.high+C.hosts*chunks C.groups C.lanes<2^w

theorem extents (r : C.Fits w) : C.root≤C.ranks.base ∧ C.ranks.base+C.hosts*(C.degree+1)≤C.decodeAt ∧
    C.lookupAt+C.count≤C.high ∧ C.high<2^w:=by
  exact ⟨(Nat.le_add_right ..).trans r.old.separate,(Nat.add_le_add_left r.length _).trans r.next.2.2,
    Nat.le_add_right ..,(Nat.le_add_right ..).trans_lt r.enough⟩

theorem any (r : C.Fits w) (m : Memory w) : (C.cpu w).Exec m (C.finalMem m) C.ticks ∧ CheapCode (C.cpu w) ∧
    ∀z,z<C.root ∨ C.high≤z→C.finalMem m z=m z:=by
  obtain ⟨old,rank,rest,space⟩:=C.extents r
  have sep : C.decodeAt≤C.lookupAt:=(Nat.le_add_right ..).trans r.static_
  have end_ : C.lookupAt+C.count<2^w:=rest.trans_lt space
  have decodeRoom:=r.static_.trans_lt ((Nat.le_add_right ..).trans_lt end_)
  obtain ⟨one,cheapOne,keep⟩:=DescentResetSignedHaloMatrix.any r.old m
  have two:=DescentOrdinaryAtomFieldRAM.ROM.run C.pages (C.signedBits*C.lanes) C.decodeAt (C.first m) decodeRoom
  have three : (DescentPackedChildNeighbor.SIMD.ROM.program C.lookupAt (C.degree+1) C.queryBits C.cargoBits
      C.lanes C.hosts C.groups w).Exec (C.second m) (C.finalMem m) (4+10*C.count) :=
    @DescentStaticWordColumn.mount w C.lookupAt C.count
      (DescentPackedChildNeighbor.SIMD.ROM.numbers (C.degree+1) C.queryBits C.cargoBits C.lanes C.hosts C.groups)
      (C.second m) end_
  refine ⟨?_,?_,?_⟩
  · intro P R K machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then (Procedure.Exec.then one two.1) three machine pc regs pubs exit rom advice cfg memory enter same
  · exact @cheap_seq w _ _ (@cheap_seq w _ _ cheapOne
      (DescentOrdinaryAtomFieldRAM.ROM.cheap C.pages (C.signedBits*C.lanes) w C.decodeAt))
      (@DescentStaticWordColumn.cheap w C.lookupAt
        (DescentPackedChildNeighbor.SIMD.ROM.numbers (C.degree+1) C.queryBits C.cargoBits C.lanes C.hosts C.groups) C.count)
  · intro z hz
    have ranksBefore : C.ranks.base≤C.decodeAt := (Nat.le_add_right ..).trans rank
    have rootBefore := old.trans ranksBefore
    have decodeEnd : C.decodeAt+C.delta≤C.high := r.static_.trans ((Nat.le_add_right ..).trans rest)
    have rankEnd := rank.trans ((Nat.le_add_right ..).trans decodeEnd)
    have firstEnd := r.old.separate.trans ((Nat.le_add_right ..).trans rankEnd)
    have finalFrame := DescentStaticWordColumn.frame C.lookupAt C.count
      (DescentPackedChildNeighbor.SIMD.ROM.numbers (C.degree+1) C.queryBits C.cargoBits C.lanes C.hosts C.groups)
      (C.second m) z (hz.imp (fun l=>l.trans_le (rootBefore.trans sep)) (fun h=>rest.trans h))
    have decoderFrame := DescentOrdinaryAtomFieldRAM.ROM.frame C.pages (C.signedBits*C.lanes) C.decodeAt (C.first m) z
      (hz.imp (fun l=>l.trans_le rootBefore) (fun h=>decodeEnd.trans h))
    exact finalFrame.trans (decoderFrame.trans (keep z (hz.imp id (fun h=>firstEnd.trans h))
      (hz.imp (fun l=>l.trans_le old) (fun h=>rankEnd.trans h))))

def native (r : C.Fits w) : NativePhase w:=⟨C.cpu w,C.ticks,C.finalMem,(C.any r (fun _=>0)).2.1⟩

/-- Every signed donor register uses identical three static tables and the one old-halo matrix. -/
theorem posted {N : ℕ} (r : C.Fits w) (m : Memory w) (p : Fin C.oldHosts→Fin C.degree→Option (Fin C.oldHosts))
    (home : Fin N→Fin C.oldHosts) (bound : N≤C.hosts) (room : N≤C.owner.size) (digitRoom : C.degree+2<2^C.cargoBits)
    (counted : m C.oldCount.base=(N:Word w)) (homes : ∀i,m (C.owner.base+i.val)=((home i).val:Word w))
    (edges : ∀v j,m (C.oldRoster.base+(v.val*C.degree+j.val))=(target (p v j):Word w))
    (portWord : Expr) (data_ : Fin C.hosts→Fin C.groups→Cell C.signedBits) (fits : portWord.Fits w C.root) (prior : Source portWord data_ C.lanes m) :
    (C.native r).Runs m ∧ (C.port portWord).Fits w C.high ∧ Source (C.port portWord)
      (fun h g=>lookup (short (b:=C.cargoBits) p home h) (askedField C.degree C.cap C.signedBits C.queryBits (data_ h g) 0) (List.finRange (C.degree+1))) C.lanes (C.finalMem m):=by
  obtain ⟨root,atRanks,atLookup,space⟩:=C.extents r
  have mid : C.ranks.base≤C.decodeAt:=(Nat.le_add_right ..).trans atRanks
  have decodeRoom : C.decodeAt+C.delta<2^w:=r.static_.trans_lt ((Nat.le_add_right ..).trans_lt (atLookup.trans_lt space))
  have old:=DescentResetSignedHaloMatrix.any r.old m
  have measured:=DescentResetSignedHaloMatrix.read r.old m p home bound room counted homes edges
  have current : Source portWord data_ C.lanes (C.first m):=fun r'=>
    (eval_below _ _ m (C.first m) fits (fun z l=>old.2.2 z (.inl l) (.inl (l.trans_le root)))).trans (prior r')
  have decoder:=decoder_run (H:=C.hosts) (G:=C.groups) (M:=C.lanes) C.degree C.cap C.signedBits C.queryBits C.decodeAt (C.first m) decodeRoom
  have projected:=decoder.2.1 portWord data_ (ProtocolRAMGeneratedWrite.fits_mono _ (root.trans mid) fits) current
  have retained (h : Fin C.hosts) (j : Fin (C.degree+1)) : C.second m (C.ranks.base+(h.val*(C.degree+1)+j.val))=(rank p home h j:Word w):=by
    have ix:h.val*(C.degree+1)+j.val<C.hosts*(C.degree+1):=(Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)
    exact (decoder.2.2.1 _ (.inl ((Nat.add_lt_add_left ix _).trans_le atRanks))).trans (measured h j)
  have dir : C.ranks.Fits w C.lookupAt:=⟨r.next.1,r.next.2.1,r.next.2.2.trans ((Nat.le_add_right ..).trans r.static_)⟩
  have outcome:=packed (a:=C.queryBits) (M:=C.lanes) (G:=C.groups) C.ranks C.lookupAt p home (C.second m) retained digitRoom dir r.length r.enough
  exact ⟨(C.any r m).1,outcome.2.1 _ _ (ProtocolRAMGeneratedWrite.fits_mono _ r.static_ projected.1) projected.2⟩

end Shelf
end
end Hierarchy.DescentResetSignedHaloMatrix

end OAI
