import OAI.Hierarchy.DescentOperandReindex
import OAI.Hierarchy.DescentRetainedSevenRead
import OAI.Hierarchy.DescentResetOperandSetup
import OAI.Hierarchy.DescentResetRetainedPlacementRead
import OAI.Hierarchy.DescentResetRetainedIssue

namespace OAI
/-! # The actual remixed node fields and earlier signed panel in one successor memory -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty.Chronology DescentSixParty.PackedFlow.Channels
open DescentGL DescentColonies DescentOrdinaryAtomFieldRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w U : ℕ} (C : DescentResetOperandSetup.Chart)

theorem source_reindexed {h g h' g' a M w : ℕ} (host : h'=h) (group : g'=g) (Y : Fin h→Fin g→Cell a)
    (src : Expr) (mem : Memory w) (fact : Source src Y M mem) :
    Source src (reindexed host group Y) M mem :=by
  subst h';subst g';exact fact

/-- Stable contents delivered by the two placement phases. Both receipts point
into the same RAM, after the original signed input has been re-read and placed. -/
structure Moved (base : ℕ) (s : C.Sources) (name : Fin U→Fin C.placement.sparse) (out : Memory w)
    (Y : Fin (C.retained.outputs*C.placement.shapes)→Fin C.placement.oldHosts→Fin (C.placement.groups*C.placement.blocks)→Cell C.retained.bits)
    (signed : Fin C.strip→Fin C.placement.oldHosts→Fin (C.placement.groups*C.placement.blocks)→Cell C.signedBits) : Prop where
  retained : ∀j x,Source (.lookup (C.seven.bank base j x) .row)
    (DescentRetainedTargetPlacement.Chart.compact C.placement C.seven.batch s.primary name Y j x) C.lanes out
  panel : ∀j x,Source (.lookup (C.placement.bank C.signedFields (C.placedSigned base) j x) .row)
    (C.placement.compact C.signedFields (fun _=>true) name signed j x) C.lanes out

/-- Both the seven predecessor fields and their donor indices use the actual home and comparison
packet from the same memory as the saved reset matrix and the earlier signed ports. -/
theorem movedSources (base : ℕ) (m : Memory w) (s : C.Sources) (ready : C.Ready s w base)
    (room : C.placed base<2^w) (host : C.placement.oldHosts=C.retained.hosts)
    (group : C.placement.groups*C.placement.blocks=C.retained.grouped)
    (size : 2^(C.retained.high+C.retained.low)=C.retained.groups*C.retained.blocks)
    (batch : 2^C.retained.low=C.retained.gatherLanes*C.retained.blocks)
    (gather : 0<C.retained.gatherLanes) (blocks : 0<C.retained.blocks) (past : 0<C.retained.previousLanes)
    (cut : C.retained.cut≤C.retained.high+C.retained.low) (pitch : C.retained.matrixLanes*C.retained.donors=2^C.retained.low)
    (matrix : 0<C.retained.matrixLanes) (decode : 0<C.retained.decodedLanes) (packetLanes : 0<C.seven.packetLanes)
    (sig : 0<C.signedLanes) (L : DescentGL.Layout (C.retained.high+C.retained.low))
    (chosen : m s.matrix.base=((DescentExterior.matrixCode L).val:Word w))
    (x : C.retained.Values) (capacity : ∀i,C.retained.hosts*chunks C.retained.groups C.retained.previousLanes≤(s.old i).size)
    (read : ∀j,Reads (s.old j) (x j) C.retained.previousLanes m)
    (X : C.seven.Packets) (packetRead : Source s.window X C.seven.packetLanes m)
    (name : Fin U→Fin C.placement.sparse) (count : m s.count.base=(U:Word w))
    (inverse : ∀i : Fin U,m (s.inverse.base+i.val)=((name i).val:Word w))
    (cu : U<2^w) (hu : C.placement.newHosts≤2^w) (iu : U≤ s.inverse.size)
    (signed : Fin C.strip→Fin C.placement.oldHosts→Fin (C.placement.groups*C.placement.blocks)→Cell C.signedBits)
    (earlier : ∀j,Source (s.signed j) (signed j) C.signedLanes m) :
    let panels := fun j=>blockValues cut (C.retained.before size x j) L
    let Y:=fun z : Fin (C.retained.outputs*C.placement.shapes)=>
      let j:=finProdFinEquiv.symm z
      reindexed host group (C.seven.decoded s.which X panels j.1 j.2)
    C.Moved base s name ((C.sources base w s).image m) Y signed :=by
  intro panels Y
  obtain ⟨a,b,c⟩:=C.before base
  obtain ⟨a0,p,q,r,done_⟩:=C.seven.intervals base
  have sr:=c.trans_lt room
  have inputs:=done_.trans_lt sr
  have controlRoom:=q.trans_lt (r.trans_lt inputs)
  have prevRoom:=p.trans_lt controlRoom
  let initial:=(C.previous base w s).image m
  let readyMem:=C.seven.prepared s.which base s.old s.matrix s.window m
  have held:=C.seven.any base s.which s.primary s.old s.matrix s.window s.count s.inverse m ready.previous
    ready.matrix ready.window ready.count ready.inverse ready.lanes ready.blocks sr
  have low (u : ℕ) (lt:u<base) : initial u=m u:=held.2.1 u (.inl lt)
  have preparedLow (u : ℕ) (lt:u<base) : readyMem u=m u:=by
    apply (ROM.frame _ _ _ _ _ (.inl (lt.trans_le ((a0.trans p).trans q)))).trans
    apply (ROM.frame _ _ _ _ _ (.inl (lt.trans_le (a0.trans p)))).trans
    apply ((C.seven.control.any s.which (C.seven.seen base) s.window (C.retained.movedImage base s.old s.matrix m)
      (ProtocolRAMGeneratedWrite.fits_mono _ a0 ready.window) controlRoom).2.2 u (.inl (lt.trans_le a0))).trans
    exact (C.retained.moved_any base s.old s.matrix m ready.previous ready.matrix prevRoom).2.1 u (.inl lt)
  have target (j : Fin (C.retained.outputs*C.placement.shapes)) :
      Source (C.seven.terms base s.which j) (Y j) C.retained.decodedLanes readyMem:=by
    apply source_reindexed host group
    exact C.seven.query_read base s.which s.old s.matrix s.window m ready.window packetLanes X packetRead panels
      (C.retained.moved_reads base s.old s.matrix m ready.previous ready.matrix prevRoom size batch
        gather blocks past cut pitch matrix L chosen x capacity read) ready.previous ready.matrix inputs
      (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  have cap {B : Bank} {n m : ℕ} (ok : B.Fits w n) (step : n≤ m) : B.Fits w m:=⟨ok.1,ok.2.1,ok.2.2.trans step⟩
  have ct : s.count.base<base:=by have p:=ready.count.1;have q:=ready.count.2.2;omega
  have iv (j : Fin U) : s.inverse.base+j.val<base:=(Nat.add_lt_add_left (j.isLt.trans_le iu) _).trans_le ready.inverse.2.2
  have sigFit (j : Fin C.strip):=(ProtocolRAMGeneratedWrite.fits_mono _ (a.trans b) (ready.signed j))
  have sigRun:=C.placement.any C.signedFields (C.placedSigned base) (fun _=>true) s.signed s.count s.inverse initial
    ready.lanes ready.blocks sigFit (cap ready.count (a.trans b)) (cap ready.inverse (a.trans b)) room
  constructor
  · intro j block
    have observed:=DescentRetainedTargetPlacement.Chart.read C.placement C.seven.batch (C.seven.place base)
      s.primary (C.seven.terms base s.which) s.count s.inverse readyMem ready.lanes decode ready.blocks
      (fun z=>C.seven.term_fits base s.which (finProdFinEquiv.symm z).2 (finProdFinEquiv.symm z).1 inputs)
      (cap ready.count a) (cap ready.inverse a) sr name ((preparedLow _ ct).trans count)
      (fun z=>(preparedLow _ (iv z)).trans (inverse z)) cu hu iu Y target j block
    have bfit:=(DescentRetainedTargetPlacement.Chart.validBank C.placement C.seven.batch (C.seven.place base) sr j block).1
    exact fun rowId=>(eval_below (.lookup (C.seven.bank base j block) .row) _ initial _ (out:=C.placedSigned base) ⟨bfit,trivial⟩ (fun z below=>sigRun.2.1 z (.inl below))).trans (observed rowId)
  · intro j block
    have retained (z : Fin C.strip) : Source (s.signed z) (signed z) C.signedLanes initial:=
      fun rowId=>(eval_below _ _ m initial (ready.signed z) low).trans (earlier z rowId)
    exact C.placement.read C.signedFields (C.placedSigned base) (fun _=>true) s.signed s.count s.inverse initial
      ready.lanes sig ready.blocks sigFit (cap ready.count (a.trans b)) (cap ready.inverse (a.trans b)) room name
      ((low _ ct).trans count) (fun z=>(low _ (iv z)).trans (inverse z)) cu hu iu signed retained j block

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
