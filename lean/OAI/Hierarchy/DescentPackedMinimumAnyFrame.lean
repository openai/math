import OAI.Hierarchy.DescentPackedMinimumAny
import OAI.Hierarchy.DescentPackedMinimumFrames

namespace OAI
/-! # Preservation of both memory intervals through a minimum search on arbitrary words -/
namespace Hierarchy.DescentPackedMinimum
open DescentSIMDLookup DescentPackedScore ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
attribute [local irreducible] Procedure.Exec
variable {a M H G w q : ℕ}

theorem any_framed (L : Layout q) (r : Fits L w a M H G) (m : Memory w) :
    ∃out,(search L w H G M).Exec m out
      ((4+q*cost L.work (H*chunks G M))+DescentFirstMinimumRAM.ticks L.result L.ledger (List.range q)) ∧
      ∀u,u<L.work ∨ L.result+q≤u → out u=m u :=by
  obtain ⟨mid,ran,scoreFrame⟩:=issue_any_framed L r m (List.finRange q)
  have pick:=DescentFirstMinimumRAM.exec L.ledger mid (List.range q) r.ledger
    (by simpa using r.room) r.word
  refine ⟨DescentFirstMinimumRAM.after L.result L.ledger mid (List.range q),?_,?_⟩
  · simpa only [search,List.length_finRange] using ran.then pick
  · intro u away
    rcases away with lower|upper
    · have below : u<L.result:=by
        have span:=r.workspace
        have ledger:=r.ledger.2.2
        omega
      exact (DescentFirstMinimumRAM.frame L.result L.ledger mid (List.range q) u below).trans (scoreFrame u (.inl lower))
    · have above : L.result+(List.range q).length≤u:=by simpa only [List.length_range] using upper
      exact (DescentFirstMinimumRAM.frame_high L.result L.ledger mid (List.range q) u above).trans (scoreFrame u (.inr (by omega)))

end
end Hierarchy.DescentPackedMinimum

end OAI
