import OAI.Hierarchy.DescentPhysicalRoleRooms
import OAI.Hierarchy.DescentNamedResetOutput

namespace OAI
/-! # Role and birth lookup shapes on the original calendar's reset output -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet : ℕ) (old : Prior) (base : ℕ)
local notation "head_" => fromBoard G S board k tail age p f g drift degree payload e previous M nextM C packet old base

theorem birth_shape (oldBlocks : old.venue.k=k) (lanes : 0<M) :
    (head_).metadata.chart.blocks≤2^(head_).venue.next.k ∧
      0<(head_).birth.placement.lanes ∧ 0<(head_).birth.placement.blocks := by
  change 2^k≤2^old.venue.k ∧ 0<M ∧ 0<2^k
  rw [oldBlocks]
  exact ⟨le_rfl,lanes,Nat.two_pow_pos _⟩

theorem transfer_shape (lanes : 0<M) :
    0<(head_).roleTransfer.lanes ∧ 0<(head_).roleTransfer.blocks :=by
  change 0<M ∧ 0<2^k
  exact ⟨lanes,Nat.two_pow_pos _⟩

/-- The three aperture summands of the actual priced census, including
the incoming signed tally and the historical fallback-root packet. -/
theorem funded_shape :
    (head_).venue.census.jobs=(head_).actor.shapes ∧
    1+(head_).venue.census.bits≤(head_).venue.census.broadcast ∧
    ((head_).middle.stencil.t+(head_).venue.census.bits)*2^(head_).middle.rootDepth≤(head_).venue.census.broadcast ∧
    1+(head_).middle.rootField*DescentFallbackPeriod.inputCount (head_).funded.degree (2^(head_).middle.rootDepth)
      (head_).funded.capacity (head_).middle.rotorBits (head_).middle.rootDepth≤(head_).venue.census.broadcast :=by
  refine ⟨rfl,?_,?_,?_⟩
  · exact Nat.le_max_left _ _
  · exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  · exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
