import OAI.Hierarchy.DescentSeedHeaderLayout
import OAI.Hierarchy.DescentSeedSourceExtent
import OAI.Hierarchy.DescentSeedNativeStartup
import OAI.Hierarchy.DescentSeedNodeChart

namespace OAI
/-! # The counted header and the role source lie inside the named startup layout -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader.Input
open DescentCompiler DescentInitialHost DescentSeedRoot DescentWideSeedFlags DescentPackedEpochShelves
open DescentPackedProfileInstall DescentSixParty DescentPackedSeed Catalyst
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g drift h : ℕ) (v : SeedHeader.Input F)
local notation "g₀" => v.schedule.groupCount 0
local notation "l" => v.layout G t f g drift h
local notation "s" => v.width G
local notation "header" => v.base G h-1

theorem initial_held_geometry (wide : 16*digitsNeeded s≤h) :
    header<(l).base ∧
      publicWords v.circuit+DescentDyadicSpan.span (DescentPackedSeed.Primitive.Source.jobs v.circuit v.schedule.copies s h)≤
        (DescentDatedSeedStartup.Input.nodeChart l v.k v.hosts g₀).seedEnd (endAddress v.circuit l v.hosts g₀ v.k) :=by
  have budgetWord:=DescentExteriorShelf.Root.role_source_extent v.circuit v.schedule.copies s h wide
  have before : endInput v.circuit v.schedule.copies s h≤v.base G h:=by
    dsimp (config := {zetaHave := true}) only [base,publicFront,selectorBase,end_,dict]
    omega
  have early : header<(l).base:=by
    change v.base G h-1<v.base G h
    have positive : 0<v.base G h:=by change 0<_+2;omega
    omega
  have alloc:=fences v.circuit l v.hosts g₀ v.k
  have order:=alloc.1.trans (alloc.2.1.trans alloc.2.2)
  have roof : endAddress v.circuit l v.hosts g₀ v.k≤
      (DescentDatedSeedStartup.Input.nodeChart l v.k v.hosts g₀).seedEnd (endAddress v.circuit l v.hosts g₀ v.k):=
    (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact ⟨early,budgetWord.trans (before.trans (order.trans roof))⟩

end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

end OAI
