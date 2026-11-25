import OAI.Hierarchy.DescentDatedWOrigin

namespace OAI
/-! Transition from a genuinely measured W inlet to the actor projections read after its vector gather. -/
namespace Hierarchy.DescentOrdinaryOriginMask
open DescentHaloWalkRAM DescentPackedActorMask DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

namespace Return
variable (R : Return) (C : Fin R.lows→Refs R.degree R.depth R.oldNodes R.capacity)
local notation "N" => nodes (breadth R.degree*2^R.depth) R.oldNodes R.capacity

theorem after_gather {w a nb mb} (initial base : ℕ) (previous current : Memory w)
    (hm : 0<R.lanes) (hr : 0<R.blocks)
    (V : Fin R.lows→Values R.degree R.depth R.oldNodes R.capacity R.hosts
      (R.groups*R.blocks) a nb mb)
    (measured : ∀i,Measured (C i) (V i) R.newNodes (R.lanes*R.blocks) initial previous)
    (le : initial≤base) (keep : ∀j< initial,current j=previous j) (space : R.finish base<2^w) :
    ∀x,Reads (R.returned base x)
      (DescentScalarBookReshape.book (fun l h g=>selection N R.newNodes R.ordinalBits (marked (V l) h g)) x)
      R.lanes (R.image C base current):=by
  have source i:=read_mask (C i) (V i) (measured i)
  have live i : Source (mask (C i)) (marked (V i)) (R.lanes*R.blocks) current:=by
    intro p
    exact (eval_below _ _ previous current (source i).1 keep).trans ((source i).2 p)
  have got i:=DescentOperandFamilyBook.issued R.law (dead N R.newNodes R.ordinalBits) (R.lanes*R.blocks) base 0
    (fun _:Fin 1=>mask (C i)) current (fun h g (_:Fin 1)=>marked (V i) h g)
    (fun _=>ProtocolRAMGeneratedWrite.fits_mono _ le (source i).1) (fun _=>live i) (R.table_before base space)
  exact R.grid.originReturned (R.rowsAt base) (R.expr C base) _ (fun i=>(got i).1) space hm hr _ (fun i=>(got i).2)

end Return
end
end Hierarchy.DescentOrdinaryOriginMask

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryOriginMask DescentOrdinaryOriginPorts DescentOperandVectorArena
open DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ScalarOperand DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem gathered_origin_ports {w a nb mb} (floor outBits : ℕ)
    (refs : References v.vector v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity)
    (C : Fin v.vector.lows→Refs v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity)
    (V : Fin v.vector.lows→Values v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
      v.vector.hosts (v.vector.groups*v.vector.radix) a nb mb) (m : Memory w)
    (room : refs.Room w (v.vectorStart floor))
    (measured : ∀i,Measured (C i) (V i) v.resolver.nodes (v.vector.lanes*v.vector.radix) (v.vectorStart floor) m)
    (space : v.originPortEnd floor<2^w) (x : Fin v.vector.radix) (node : Fin v.resolver.nodes) (f : Fin 6) :
    let data_:=DescentScalarBookReshape.book (fun l h g=>selection v.originCandidates v.resolver.nodes v.originBits (marked (V l) h g)) x
    let first:=refs.phase w (v.vectorStart floor)
    (v.originPort floor outBits x node f).Fits w (v.originPortEnd floor) ∧
      Source (v.originPort floor outBits x node f) (fun h g=>readLaw v.originChart outBits node f (data_ h g)) v.vector.lanes
        ((v.originPrefix floor outBits w C).image (first.image m)):=by
  intro data_ first
  have before : v.originPortFloor floor<2^w:=(Nat.le_add_right _ _).trans_lt space
  have traced:=refs.any (v.vectorStart floor) m room
  have got:=v.originChart.after_gather C (v.vectorStart floor) (v.routedStart floor) m (first.image m)
    room.lanes room.radix V measured (v.vector_before floor) (fun z hz=>traced.2 z (.inl hz)) before x
  have bank:=v.originChart.grid.returned_fits (v.originChart.rowsAt (v.routedStart floor)) x before
  exact DescentOrdinaryOriginPorts.issued v.originChart outBits _ _ _ x node f data_ bank.1 bank.2 got space

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
