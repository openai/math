import OAI.Hierarchy.DescentDatedPrimitiveUpdate
import OAI.Hierarchy.DescentOrdinaryRoleRetileRate
import OAI.Hierarchy.DescentOrdinaryOriginPrice
import OAI.Hierarchy.DescentPackedMatchedAll

namespace OAI
/-! The fixed-age primitive update pays for all four repitches, actual ROM contents, halo probes, and final origin selection. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPacking.PackedMatch.Local DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSixParty.Chronology
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {w : ℕ}

def invoice (p : NativePhase w) :=p.ticks+7*names p.program
theorem invoice_seq (p q : NativePhase w) : invoice (p.seq q)=invoice p+invoice q:=by
  simp only [invoice,NativePhase.seq,names_seq,Nat.mul_add];omega

namespace Shape
variable (C : Shape)
def fee :=(4+10*(2*2^C.width))+(4+C.blocks*(4+C.rows*(2*25+4)))+
  7*((15*(2*2^C.width+1))+(15+C.blocks*(11+4*25)))

theorem fee_le (base : ℕ) (ids pool : Fin C.blocks→Bank) :
    invoice (C.phase base ids pool w)≤C.fee:=by
  have scan:=DescentOperandVectorArena.names_passes (C.output base) C.rows C.rows w 25 (C.term base ids pool) 0 C.blocks (by
    intro n _ hi
    have small : n<C.blocks:=by omega
    simp only [term, dite_eq_left small, DescentPackedZip.work, Expr.work]; decide)
  have clock:=C.clock_le (w:=w) base ids pool
  unfold invoice fee
  apply Nat.add_le_add clock (Nat.mul_le_mul_left 7 ?_)
  simp only [phase,names_seq,ROM.mount,names_mount]
  exact Nat.add_le_add_left scan _
end Shape

namespace Layout
variable (L : Layout) (base : ℕ) (B : L.Inputs)
local notation "ref" => L.references (L.bookStart base)
local notation "sp" => L.spread
local notation "K" => 1+L.candidates*61
local notation "cells" => DescentScalarBookReshape.cells L.hosts L.lows L.groups L.blocks (sp).bits L.workLanes

def lookupFee (R : DescentOrdinaryRoleRetile.Layout) :=4096*(R.lookupBill+R.rowBill)
def literalFee (n : ℕ) :=4+10*n+7*(15*(n+1))
def gatherFee := (4+L.lows*(4+(sp).rows*(2*(K)+4)))+((4+10*cells)+(4+L.blocks*(sp).nextRows*54))+
  7*((15+L.lows*(11+4*(K)))+(15*(cells+1)+111))
def paid :=
  lookupFee L.prior+lookupFee L.births+lookupFee L.origins+
  literalFee (DescentScalarHaloPortROM.length L.hosts L.oldGroups L.oldWork L.ports)+
  (literalFee (L.references 0).digitSize+literalFee (L.references 0).tableSize)+
  L.gatherFee+L.join.fee+lookupFee L.durable

private theorem operand_work {p r cap k : ℕ} (ports : Ports p) (old : Fin r → Bank)
    (fresh : Fin r → Fin cap → Fin 6 → Bank) (dict : Fin k → Bank)
    (hosts : ℕ) (rack : Fin p) (block : Fin r) (j : Fin (k + cap * 6)) :
    (operand ports old fresh dict hosts rack block j).work ≤ 50 := by
  unfold operand
  cases finSumFinEquiv.symm j <;>
    simp only [Sum.elim_inl, Sum.elim_inr, project, peerExpr, neighborID, Expr.work] <;> decide

set_option maxHeartbeats 1200000 in
theorem paid_le (hp : 0<L.priorLanes) (hb : 0<L.birthLanes) (ho : 0<L.originLanes)
    (hw : 0<L.workLanes) (hn : 0<L.nextLanes) : invoice (L.phase base B w)≤L.paid:=by
  have live : 0<L.oldWork:=Nat.mul_pos hw (Nat.two_pow_pos _)
  have old:=L.prior.shared_fee base B.previous w hp live
  have born:=L.births.shared_fee (L.birthStart base) B.newborn w hb live
  have orig:=L.origins.shared_fee (L.originStart base) B.origin w ho hw
  have last:=L.durable.shared_fee (L.durableStart base) (L.join.bank (L.joinStart base)) w hw hn
  have port : invoice (L.portPhase base w)=literalFee (DescentScalarHaloPortROM.length L.hosts L.oldGroups L.oldWork L.ports):=by
    simp only [invoice,portPhase,DescentScalarHaloPortROM.program,names_mount,literalFee]
  have refs : invoice (L.refPhase base w)=literalFee (L.references 0).digitSize+literalFee (L.references 0).tableSize:=by
    simp only [invoice,refPhase,DescentOrdinaryRefsROM.Chart.program,names_seq,ROM.mount,names_mount,literalFee]
    change ((4+10*(ref).digitSize)+(4+10*(ref).tableSize))+
      7*(15*((ref).digitSize+1)+15*((ref).tableSize+1))=
        (4+10*(ref).digitSize+7*(15*((ref).digitSize+1)))+
          (4+10*(ref).tableSize+7*(15*((ref).tableSize+1)))
    ring
  have field (j : Fin L.candidates) : (L.field base B j).work≤50:=by
    exact operand_work _ _ _ _ _ _ _ _
  have gathered : (L.pool base B).work≤(K):=by
    simpa only [pool, Gather.assembly, List.length_finRange, DescentOrdinaryRefsROM.Chart.nodes, DescentOrdinaryRefsROM.Chart.donors, references, candidates, ports, blocks, DescentHaloWalkRAM.breadth] using Gather.collect_work (ref).gates (L.field base B) (List.finRange _) 50 field
  have pool : invoice (L.poolPhase base B w)≤L.gatherFee:=
    (sp).invoice w (L.spreadStart base) (K) (fun _=>L.pool base B) (fun _=>gathered)
  have chosen:=L.join.fee_le (w:=w) (L.joinStart base) (L.origins.bank (L.originStart base)) ((sp).returned (L.spreadStart base))
  simp only [phase,head,invoice_seq,paid,port,refs]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add old born) orig) _) _) pool) chosen) last

end Layout
end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint DescentStaticWordColumn
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
  (A : ArgumentEntry v) (r : A.Match v floor) (radix : v.vector.radix=2^v.reference.k)
noncomputable section
def primitiveBill :=DescentOrdinaryPaletteBirth.cpu v.bornBook+7*DescentOrdinaryPaletteBirth.textCost v.bornBook+v.paletteShape.paid

theorem primitive_charge {w : ℕ} (hp : 0<v.rasterLanes) (hb : 0<v.bornBook.lanes)
    (ho : 0<v.vector.lanes) (hw : 0<v.palette.workLanes) (hn : 0<v.palette.nextLanes) :
    invoice (v.primitiveUpdate floor A r radix w)≤v.primitiveBill:=by
  rw [primitiveUpdate,invoice_seq]
  apply Nat.add_le_add _ (v.paletteShape.paid_le _ _ hp hb ho hw hn)
  have h:=DescentOrdinaryPaletteBirth.price v.gadget v.palette.seedWidth v.palette.grainLimit v.palette.rotor
    v.bornBook (A.chipBank v floor) (v.operandEnd floor) w
  exact Nat.add_le_add h.1 (Nat.mul_le_mul_left 7 h.2)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
