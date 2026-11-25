import OAI.Hierarchy.DescentProfiledOrdinaryOffer
import OAI.Hierarchy.DescentRegisteredVenuePitchBounds
import OAI.Hierarchy.DescentDatedReturnMetadata

namespace OAI
/-! Scalar widths of the final metadata at a family of ordinary dates
whose logarithmic divisors and tail rates may differ. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology DescentDatedAddressBook DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift degreeMax : ℕ)
    {ι : ℕ → Type*} (tailRate budget : ∀h, ι h → ℕ)
    (point : ∀h (i : ι h), ProfiledOrdinaryOffer G f g board op t reset (tailRate h i) drift degreeMax (budget h i) h)
local notation "m_" h:arg i:arg => (point h i).model.metadata
local notation "r_" h:arg i:arg => (point h i).model.resolver
local notation "J_" h:arg i:arg => Nat.log 2 h/(2*budget h i)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h i) f g reset (point h i).slot.sites (tail (tailRate h i) (J_ h i))

theorem metadata_from_resolver (R : DescentDatedPriorOperand.Layout.ScalarRoom (fun h i => r_ h i)) :
    MetadataReturn.ScalarRoom (fun h i => m_ h i) ∧
    ∃K : ℕ, ∀ᶠ h : ℕ in atTop, ∀i : ι h, ((m_ h i).spanBits*(m_ h i).chart.nodes)*(m_ h i).chart.lanes≤K*h := by
  refine ⟨⟨⟨R.blocks,R.nodes,R.hosts,R.groups,R.lanes,2,?_⟩,1,?_⟩,1,?_⟩
  · apply Eventually.of_forall
    intro h i
    let v := r_ h i
    change ((v.size+2)*v.nodes+(v.size+2))*v.lanes≤2*h
    have packed := (point h i).prices.prior
    have full := (point h i).prices.resolve
    change ((v.size+2)*v.nodes)*v.lanes≤h at packed
    change (11*(v.size+2))*v.lanes≤h at full
    rw [Nat.add_mul]
    have lite : (v.size+2)*v.lanes≤h :=
      (Nat.mul_le_mul_right v.lanes (Nat.le_mul_of_pos_left _ (by decide : 0<11))).trans full
    omega
  · apply Eventually.of_forall
    intro h i
    let v := r_ h i
    change max ((S_ h i).censusBits (point h i).slot.p) ((v.size+2)+(v.size+2))*v.lanes≤1*h
    let x := point h i
    have fee := (PhysicalOrdinary.registered_venue_pitch x.books x.cut.ticket g (tail (tailRate h i) (J_ h i))
      x.slot.p f h (x.slot.menu.seats x.slot.age) x.slot.position.ports.venue.lanes
      x.slot.position.ports.io.roster x.slot.menu.ordinary x.slot.position.ports x.stageFloor).2.2
    have full := (point h i).prices.resolve
    change (11*(v.size+2))*v.lanes≤h at full
    rw [← Nat.mul_max_mul_right,Nat.one_mul]
    exact max_le (fee.trans (Nat.div_le_self ..)) ((Nat.mul_le_mul_right _ (by omega)).trans full)
  · apply Eventually.of_forall
    intro h i
    rw [Nat.one_mul]
    change (((r_ h i).size+2)*(r_ h i).nodes)*(r_ h i).lanes ≤ h
    exact (point h i).prices.prior

theorem final_roofs_from_rooms (R : PhysicalOrdinary.OperandRooms (fun h i => (point h i).model)) :
    Bounded (fun h i => (m_ h i).ordinaryEnd 0+(point h i).model.operandBook.endAddress 0) := by
  have metadata := metadata_from_resolver G board op t f g reset drift degreeMax tailRate budget point R.resolver
  exact (MetadataReturn.ordinary_rate _ metadata.1 metadata.2).add (DescentOrdinaryFinal.Chart.extent_rate _ R.finalBook)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
