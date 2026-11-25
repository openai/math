import OAI.Hierarchy.DescentOriginalArgumentPointer
import OAI.Hierarchy.DescentPrivateOldDonors

namespace OAI
/-! # The reached pointer at a genuine public entry of the chronological operand list -/
namespace Hierarchy.DescentSixParty.Reached
open DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentCompiler
open Computability.BorderVNP.Crossing ThreeFlat.Routing
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist p R : ℕ}
    (cap : Reached W G q ε S k age grain degree wire hist) (hp : 0<p) (pin : P→ℕ)

def publicPointer (v : W.graph.Site) (ref : BlockRef p (boundaryWidth W.graph v)) : DescentOperandStateBanks.Pointer :=
  match ref with
  | ⟨.inl edge,chunk,fits⟩ => firstCable cap hp v edge chunk fits
  | ⟨.inr port,chunk,_⟩ => .pin (pin port.val) chunk

theorem argument_public (B : BitDescription W) (rank : Local B) (shape : WorldShape p R B) (arity : ℕ)
    (v : W.graph.Site) (u : (B.recipe v).Node) (j : ℕ) (ref : BlockRef p (boundaryWidth W.graph v))
    (key : ((shape.sites v).keys u)[j]?=some (.inl ref)) :
    argumentPointer cap B rank shape hp pin arity ⟨v,u⟩ j=publicPointer cap hp pin v ref :=by
  have hit : j<((shape.sites v).keys u).length:=by
    by_contra! past
    simp [List.getElem?_eq_none past] at key
  have at_:=Option.some.inj ((List.getElem?_eq_getElem hit).symm.trans key)
  have typed : ((shape.sites v).recipe hp).operand u ⟨j,hit⟩=.inl ref :=by
    change ((shape.sites v).keys u)[j].map id _=_
    rw [at_];rfl
  rcases ref with ⟨edge | port,chunk,fits⟩
  · exact argumentPointer_cable cap B rank shape hp pin arity v u ⟨j,hit⟩ edge chunk fits typed
  · exact argumentPointer_pin cap B rank shape hp pin arity v u ⟨j,hit⟩ port chunk fits typed

end
end Hierarchy.DescentSixParty.Reached

end OAI
