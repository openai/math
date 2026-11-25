import OAI.Hierarchy.DescentScalarVenueReceiver
import OAI.Hierarchy.DescentScalarActorPublisherROM
import OAI.Hierarchy.DescentScalarBookColumns
import OAI.Hierarchy.DescentPackedMatchedAll

namespace OAI
/-! # Intrinsic program names and clock for the ordinary scalar venue word -/
namespace Hierarchy.DescentScalarVenueMask.Tariff
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local DescentSharedCableNames DescentPackedColony
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentStaticWordColumn
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {P r cap H G M w : ℕ}
local notation "A"=>DescentPackedActorMask.actors (P*r) cap
local notation "K"=>1+cap*6

/-- No unrolled host loop occurs in a recipient expression; donors and
bounded relative paths supply its only variable factors. -/
theorem receipt (C : Donors P r cap) (H : ℕ) : (C.all H).work≤1+A*(C.hub.work+100+100*P):=by
  have each (j:Fin A) : (C.one H j).work≤C.hub.work+89+100*P:=by
    let z:Fin (P*r)×Fin K:=finProdFinEquiv.symm j;let x:Fin P×Fin r:=finProdFinEquiv.symm z.1
    have walk:=DescentPackedChildNeighbor.SIMD.work (C.head x.1).host (peerExpr C.ports (C.route x.2 z.2) H x.1) (List.finRange P)
    have route_ : (peerExpr C.ports (C.route x.2 z.2) H x.1).work≤64:=by simp only [peerExpr,neighborID,Expr.work]; decide
    have key_ : (peerExpr C.ports (C.localKey x.2 z.2) H x.1).work≤64:=by simp only [peerExpr,neighborID,Expr.work]; decide
    simp only [Donors.one,expr,DescentPackedZip.work]
    dsimp only [x,z] at walk route_ key_
    rw [walk,List.length_finRange]
    nlinarith only [key_,route_,Nat.mul_le_mul_left P (Nat.add_le_add_right route_ 36)]
  simpa only [Donors.all,Gather.assembly,List.length_finRange,Nat.add_assoc,show 89+100*P+11=100+100*P from by omega] using
    Gather.collect_work C.masks (C.one H) (List.finRange A) (C.hub.work+89+100*P) each

theorem publish (C : Publisher.Chart r cap) (base H G M w : ℕ) :
    let ps:=Publisher.passes C H G M base;let n:=H*chunks G M;let count:=2*(r*K)
    clock ps≤4+count*(4+n*64) ∧ names (ProtocolRAM.program w ps)≤15+count*131:=by
  intro ps n count
  have terms:∀e∈Publisher.expressions C,e.work≤30:=by
    intro e he;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
    unfold Publisher.expr;rw [DescentPackedZip.work]
    cases h:finSumFinEquiv.symm ((Publisher.index r cap).symm i).2.2 <;> change 25 ≤ 30 <;> decide
  constructor
  · simpa only [ps,count,n,Publisher.passes,Publisher.expressions,List.length_ofFn] using ProbeStage.Native.columns_clock n base 30 (Publisher.expressions C) terms
  · simpa only [ps,count,n,Publisher.passes,Publisher.expressions,List.length_ofFn,names] using labels_registers (Publisher.expressions C) base n 30 w terms

theorem directory (C : DescentScalarVenueDirectory.Chart) (base H P w : ℕ) :
    let ps:=DescentScalarVenueDirectory.passes C base H P
    clock ps≤4+P*(4+(H*P)*260) ∧ names (ProtocolRAM.program w ps)≤15+P*523:=by
  intro ps
  let es:=List.ofFn (DescentScalarVenueDirectory.expression C H : Fin P→Expr)
  have terms:∀e∈es,e.work≤128:=by intro e he;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he;simp only [DescentScalarVenueDirectory.expression,DescentScalarVenueDirectory.donor,Expr.work]; decide
  constructor
  · simpa only [ps,DescentScalarVenueDirectory.passes,es,List.length_ofFn] using ProbeStage.Native.columns_clock (H*P) base 128 es terms
  · simpa only [ps,DescentScalarVenueDirectory.passes,es,List.length_ofFn,names] using labels_registers es base (H*P) 128 w terms

/-- Fixed program memory includes every literal mask and lookup entry.
The only wide physical loop runs over the public host/chunk rows. -/
theorem headers (sorted ends : Bank) (base H G M P w : ℕ) :
    let n:=DescentScalarVenueDirectory.ROM.size H P;let cost:=DescentPackedChildNeighbor.SIMD.ROM.cells P (Packed.bits P) 1 M H G
    Headers.ticks sorted ends base H G M P ≤ (4+10*n)+(4+P*(4+H*P*260))+(4+10*cost) ∧
      names (Headers.code sorted ends base H G M P w) ≤ 15*(n+1)+(15+P*523)+15*(cost+1):=by
  intro n cost;have b:=directory (DescentScalarVenueDirectory.ROM.chart sorted ends base H P) (Headers.start base H P) H P w
  constructor
  · exact Nat.add_le_add_right (Nat.add_le_add_left b.1 _) _
  · simp only [Headers.code,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount,DescentPackedChildNeighbor.SIMD.ROM.hardware]
    exact Nat.add_le_add_right (Nat.add_le_add_left b.2 _) _

end
end Hierarchy.DescentScalarVenueMask.Tariff

end OAI
