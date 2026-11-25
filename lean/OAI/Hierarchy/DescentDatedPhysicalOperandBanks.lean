import OAI.Hierarchy.DescentDatedResolvedOrdinary
import OAI.Hierarchy.DescentDatedOperandBanks

namespace OAI
/-! # The public ordinary receiver at the actual seven-field vector allocator -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedPriorOperand DescentSIMDLookup DescentOperandStateBanks ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def vectorOutput (floor : ℕ) :=v.vector.out (v.vectorStart floor)

structure VectorShape (v : PhysicalOrdinary F P) : Prop where
  operands : v.resolver.operands=v.vector.operands
  blocks : v.resolver.blocks=v.vector.radix
  hosts : v.resolver.hosts=v.vector.hosts*v.vector.lows
  groups : v.resolver.groups=v.vector.groups
  lanes : v.resolver.lanes=v.vector.lanes

variable (floor : ℕ) (side : Fin v.resolver.jobs→Fin 6→Bank) (route : Fin v.resolver.jobs→Fin 3→Bank)

def operandBanks :=fromVector v.resolver (v.vectorOutput floor) side route

theorem operand_early {w : ℕ} («matching» : v.VectorShape) (space : v.endAddress floor<2^w)
    (sideRoom : ∀j i,(side j i).Fits w (v.normalizedEnd floor) ∧ v.resolver.rows≤(side j i).size)
    (routeRoom : ∀j i,(route j i).Fits w (v.normalizedEnd floor) ∧ v.resolver.rows≤(route j i).size) :
    (v.operandBanks floor side route).Early (v.normalizedEnd floor) w :=by
  refine ⟨?_,sideRoom,routeRoom⟩
  intro j p
  obtain ⟨fit,sz⟩:=from_previous_placed v.resolver v.vector (v.vectorStart floor) «matching».operands «matching».blocks
    «matching».hosts «matching».groups «matching».lanes ((v.routed_le floor).trans_lt ((v.resolver.floor_le (v.normalizedEnd floor)).trans_lt space))
    (v.resolver.index.symm j).1 p
  exact ⟨⟨fit.1,fit.2.1,fit.2.2.trans (v.routed_le floor)⟩,sz⟩

/-- The previous vector's allocated block banks determine every old address
of the schedule even on malformed RAM. Side and routing inputs are absolute
addresses from the already-issued six descriptor and three ticket columns. -/
theorem operand_any_from_vector {w : ℕ} (m : Memory w) («matching» : v.VectorShape)
    (sideRoom : ∀j i,(side j i).Fits w (v.normalizedEnd floor) ∧ v.resolver.rows≤(side j i).size)
    (routeRoom : ∀j i,(route j i).Fits w (v.normalizedEnd floor) ∧ v.resolver.rows≤(route j i).size)
    (space : v.endAddress floor<2^w) (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2) :
    let t:=v.operandBanks floor side route
    let cpu:=v.operandProgram t w floor
    let done:=v.operandState t floor m
    cpu.Exec m done (v.operandTicks t floor) ∧ (∀a,a<v.normalizedEnd floor ∨ v.endAddress floor≤a→done a=m a) ∧ CheapCode cpu :=
  v.operand_any _ floor m (v.operand_early floor side route «matching» space sideRoom routeRoom) space wide

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
