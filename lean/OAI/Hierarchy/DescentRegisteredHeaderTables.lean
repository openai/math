import OAI.Hierarchy.DescentRegisteredPointerOrigins

namespace OAI
/-! The two native banks consumed by the argument writer on its metadata snapshot. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentDatedPriorOperand DescentOperandStateBanks
open DescentPackedColony DescentPackedOperand DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P) (floor:ℕ) {w:ℕ} (m:Memory w)

structure HeaderTables where
  jobs : Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver
  old : Books v.resolver
  keys : ∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) j)
    (fun h g=>word ((jobs j).compiled h g)) v.resolver.lanes m
  rows : ∀x pg,Reads (previousBank v.resolver (v.vectorOutput floor) x pg) (old x pg) v.resolver.lanes m

def HeaderTables.from_reads {jobs : Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver}
    {old : Books v.resolver}
    (keys : ∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) j)
      (fun h g=>word ((jobs j).compiled h g)) v.resolver.lanes m)
    (rows : ∀x pg,Reads (previousBank v.resolver (v.vectorOutput floor) x pg) (old x pg) v.resolver.lanes m) :
    HeaderTables v floor m :=⟨jobs,old,keys,rows⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
