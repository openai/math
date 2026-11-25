import OAI.Hierarchy.DescentPhysicalRecordedVenueRoom
import OAI.Hierarchy.DescentNamedResetOutput

namespace OAI
/-! # The original reset calendar dimensions are the dimensions of its actual actor scene -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet : ℕ) (old : Prior) (base : ℕ)
local notation "head_" => fromBoard G S board k tail age p f g drift degree payload e previous M nextM C packet old base

theorem venue_faces (oldHosts:old.venue.hosts=S.hostSize age)(oldBlocks:old.venue.k=k)
    (groups:S.baseGroups=2^tail)(radix:S.radix=2^k)(within:age<S.length)(positive:0<M):
    let v₀:=head_
    v₀.venue=ResetVenue.collect old.venue v₀.venue.census v₀.actor v₀.receiver nextM ∧
    v₀.venue.census.jobs=v₀.actor.shapes ∧ v₀.venue.census.hosts=v₀.actor.hosts ∧
    v₀.venue.census.groups=v₀.actor.groups ∧ v₀.receiver.blocks=2^old.venue.k ∧
    v₀.receiver.groups*v₀.receiver.blocks=v₀.venue.census.groups ∧ 0<v₀.receiver.lanes:=by
  intro v₀
  refine ⟨rfl,rfl,oldHosts,rfl,?_,?_,positive⟩
  · change 2^k=2^old.venue.k
    rw [oldBlocks]
  · change S.groupCount (age+1)*2^k=2^(S.groupWidth k tail age)
    rw [S.group_cut within,pow_add,S.group_power groups radix]

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
