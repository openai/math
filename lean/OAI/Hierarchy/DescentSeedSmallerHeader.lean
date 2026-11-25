import OAI.Hierarchy.DescentSeedHeaderLayout
import OAI.Hierarchy.DescentTerminalAppendixBinMonotone

namespace OAI
/-! # Address of the voted header when the actual terminal input uses fewer chip bins -/
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

theorem smaller_appendix_header (size : K≤v.appendix.bins) :
    front+extra≤v.base G h-1 ∧ front+extra+votes<v.base G h-1 :=by
  have low:=DescentTerminalPublicIdentity.total_mono_bins size v.appendix.binWidth v.appendix.arity
    v.appendix.piece v.appendix.codes v.appendix.raw publicRows
  have cover : front+extra≤front+v.appendix.words publicRows:=Nat.add_le_add_left low _
  have space:=v.header_after_votes G h
  exact ⟨cover.trans space.1,(Nat.add_le_add_right cover _).trans_lt space.2⟩

end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

end OAI
