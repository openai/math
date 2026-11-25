import OAI.Hierarchy.DescentDatedSourcePathDirectory
import OAI.Hierarchy.DescentDatedPriorHeaderReceipt

namespace OAI
/-! # Original prior-header input to the per-host source-path directory -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentDatedAddressBook DescentHaloWalkRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M D : ℕ}

def nativeBanks (H G M D base : ℕ) : Banks :=
  ⟨PriorHeader.visited H G M D base,PriorHeader.priorEnds H G M D base⟩

theorem native_reads (base : ℕ) (adj : Bank) (ok : PriorHeader.Room adj H G M D base w)
    (m : Memory w) (R : Fin H → Fin D → Option (Fin H))
    (old : ∀v j,m (adj.base+v.val*D+j.val)=(number (R v j):Word w)) :
    Reads (nativeBanks H G M D base) (Gather.reaching R) (PriorHeader.image H G M D base adj m) :=
  ⟨PriorHeader.visits base adj ok m R old,PriorHeader.octets base adj ok m R old⟩

def shortPath (j : Fin (D+1)) : Fin (breadth D) :=
  finFunctionFinEquiv (![j,Fin.last D,Fin.last D,Fin.last D] : Path D)

theorem short_reaches (R : Fin H → Fin D → Option (Fin H)) (v : Fin H) (j : Fin (D+1)) :
    Gather.reaching R v (shortPath j)=DescentHaloWalkRAM.step R (some v) j := by
  simp only [Gather.reaching,shortPath,path,Equiv.symm_apply_apply]
  change DescentHaloWalkRAM.step R (DescentHaloWalkRAM.step R
    (DescentHaloWalkRAM.step R (DescentHaloWalkRAM.step R (some v) j) (Fin.last D)) (Fin.last D)) (Fin.last D)=_
  simp [DescentHaloWalkRAM.step]

/-- A source-side operand stays at its old actor's home. A target-side
operand reads the old source through the peer slot recorded in its header. -/
theorem located_stay (R : Fin H → Fin D → Option (Fin H)) (v actor : Fin H) (p q : Fin (breadth D))
    (home : Gather.reaching R v p=some actor) (issued : Gather.select (Gather.reaching R) v q=some actor) :
    value (Gather.reaching R) v p (shortPath (Fin.last D))=q.val+1 := by
  apply located _ _ actor actor _ _ _ home _ issued
  simp [short_reaches,DescentHaloWalkRAM.step]

theorem located_peer (R : Fin H → Fin D → Option (Fin H)) (v actor source : Fin H) (p q : Fin (breadth D))
    (j : Fin D) (home : Gather.reaching R v p=some actor) (peer : R actor j=some source)
    (issued : Gather.select (Gather.reaching R) v q=some source) :
    value (Gather.reaching R) v p (shortPath j.castSucc)=q.val+1 := by
  apply located _ _ actor source _ _ _ home _ issued
  simpa [short_reaches,DescentHaloWalkRAM.step,j.isLt] using peer

end
end Hierarchy.DescentDatedSourcePathDirectory

end OAI
