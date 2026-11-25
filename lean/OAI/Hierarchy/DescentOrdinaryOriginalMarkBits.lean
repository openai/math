import OAI.Hierarchy.DescentPrivateNativeDate
import OAI.Hierarchy.DescentOrdinaryMarkPhase
import OAI.Hierarchy.DescentOrdinaryResidentMark

namespace OAI
/-! The old signed panel and the scheduled group determine the mark input for every ordinary socket. -/
namespace Hierarchy.DescentSixParty.Chronology.MeterPort
open DescentSharedCableNames DescentHaloWalkRAM DescentHostDegree DescentPacking.PackedMatch.Local
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {W : MarkedWorld F d P bits} {S : DescentCompiler.AtomSchedule} {q ε : ℝ}
  {k i z D wire hist : ℕ} {prior : Reached W G q ε S k i z D wire hist}

def originalMarks (port : MeterPort prior) (nextHosts : ℕ)
    (roster : Fin port.hosts→Fin prior.placement.degree→Option (Fin port.hosts))
    (age : i<S.length) (radix : S.radix=2^k) :
    Fin (2^k)→Fin (breadth prior.placement.degree*(2^k*prior.placement.cap*11))→
      Fin nextHosts→Fin (S.groupCount (i+1))→Cell 1 :=
  let panel:=DescentOrdinarySignedMeta.donorPanel W G prior.placement (prior.order.trans Fin.valEmbedding)
    S prior.valid (DescentStageEdgeReceipt.groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding))
    (fun h:Fin port.hosts=>if hit:∃v,port.vertex v=h then some hit.choose else none)
    (fun t:Fin (S.groupCount (i+1)*2^k)=>(S.groupDigits age radix).symm (finProdFinEquiv.symm t))
  let newRole:=fun o:Fin (2^k*prior.placement.cap*11)=>
    decide ((finProdFinEquiv.symm o:Fin (2^k*prior.placement.cap)×Fin 11).2.val≠0)
  DescentOrdinaryMarkProject.bits (Gather.select (Gather.reaching roster)) panel newRole
    ((2^(k+1)-1)*(2^packExponent 20 prior.placement.degree+2))
end
end Hierarchy.DescentSixParty.Chronology.MeterPort

end OAI
