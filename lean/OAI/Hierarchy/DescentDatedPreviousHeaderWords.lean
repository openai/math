import OAI.Hierarchy.DescentOrdinaryVectorBookRead
import OAI.Hierarchy.DescentDatedOperandHeaderPair

namespace OAI
/-! The four old-node columns of an operand are the authenticated outputs of the same W gather. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOperandVectorArena DescentDatedPriorOperand DescentOperandStateBanks DescentSIMDLookup
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPackedColony DescentDatedAddressBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (shape : v.VectorShape)
    {D k K cap nb mb w : ℕ}
variable (V : References.Rows v.vector D k K cap (v.resolver.size+2) nb mb)

def previousHeaderValue (j : Fin v.resolver.jobs) (f : Fin 4) :
    DescentDatedOperandReadPipeline.Values v.ticketReadGeometry ((v.resolver.size+2)*v.resolver.nodes) :=
  let z:=v.resolver.index.symm j
  previousValues v.resolver v.vector shape.operands shape.blocks shape.hosts shape.groups
    (References.returnedValue v.vector V v.resolver.nodes) (page (f.castLE (by decide : 4≤7)) z.2.2) z.1

theorem previous_header_words (C : References v.vector D k K cap) (floor : ℕ) (m : Memory w)
    (bits : v.vector.bookBits=(v.resolver.size+2)*v.resolver.nodes)
    (pitch : 0<v.vector.lanes) (radix : 0<v.vector.radix)
    (measured : ∀p q,Measured (C p q) (V p q) v.resolver.nodes (v.vector.lanes*v.vector.radix)
      (v.vectorStart floor) m)
    (room : v.routedStart floor<2^w) :
    let done:=(C.phase w (v.vectorStart floor)).image m
    ∀j f,(v.previousAt floor j f).Fits w (v.routedStart floor) ∧
      v.resolver.rows≤(v.previousAt floor j f).size ∧
      Reads (v.previousAt floor j f) (v.previousHeaderValue shape V j f) v.resolver.lanes done :=by
  have real:=References.reads v.vector C V v.resolver.nodes (v.vectorStart floor) m bits pitch radix measured room
  have pages:=previous_values_read v.resolver v.vector shape.operands shape.blocks shape.hosts shape.groups shape.lanes
    (References.returnedValue v.vector V v.resolver.nodes) (v.vectorStart floor) _ real
  intro done j f
  let z:=v.resolver.index.symm j
  let key:=page (f.castLE (by decide : 4≤7)) z.2.2
  have placed:=from_previous_placed v.resolver v.vector (v.vectorStart floor) shape.operands shape.blocks shape.hosts
    shape.groups shape.lanes room z.1 key
  exact ⟨placed.1,placed.2,pages key z.1⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
