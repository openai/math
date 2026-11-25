import OAI.Hierarchy.DescentSeedHeaderAddressOrder
import OAI.Hierarchy.DescentSeedVoteEnd
import OAI.Hierarchy.DescentSeedSmallerHeader

namespace OAI
/-! # Original seed-header placement when the paid shell reserves a spare complete chip bin -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader.Input
open DescentSixParty DescentWideSeedFlags DescentInitialHost DescentExterior DescentPackedEpochShelves
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] (v : SeedHeader.Input F) (G : PoweredGadget F) (h K : ℕ)
local notation "front" => publicFront v.circuit v.schedule.copies (v.width G) h G.C v.steps v.j v.rest
local notation "publicRows" => ExteriorCount v.circuit*2^(v.j+v.rest)
local notation "extra" => DescentTerminalPublicIdentity.total K v.appendix.binWidth v.appendix.arity
  v.appendix.piece v.appendix.codes v.appendix.raw publicRows
local notation "lo" => selectorBase v.circuit v.schedule.copies (v.width G) h v.steps.length
local notation "pitch" => grain (h/2) G.C
local notation "votes" => ((shelves pitch lo 0 v.steps).map (stepRows pitch)).sum

theorem smaller_appendix_floor (op : RotorSpec) (t f g drift : ℕ) (size : K≤v.appendix.bins) :
    front+extra≤v.floor G op t f g drift h :=
  (v.smaller_appendix_header G h K size).1.trans ((Nat.sub_le ..).trans (v.base_le_floor G op t f g drift h))

/-- Every vote word the smaller physical proposal writes precedes the selected
paid seed header, and hence the address of the latest registered calendar. -/
theorem smaller_appendix_replay (op : RotorSpec) (t f g drift replay : ℕ)
    (size : K≤v.appendix.bins) (past : v.floor G op t f g drift h≤replay) :
    front+extra≤replay ∧ finalAt (front+extra) lo pitch v.steps<replay :=by
  have a:=v.smaller_appendix_header G h K size
  have b:=v.base_le_floor G op t f g drift h
  exact ⟨(v.smaller_appendix_floor G h K op t f g drift size).trans past,
    a.2.trans_le ((Nat.sub_le ..).trans (b.trans past))⟩

end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

end OAI
