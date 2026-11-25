import OAI.Hierarchy.DescentSeedHeaderAddressOrder
import OAI.Hierarchy.DescentSeedHeaderEnvelope

namespace OAI
/-! # The actual voted seed address above the installed exterior and public appendix -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader.Input
open DescentSixParty DescentCompiler DescentSeedRoot DescentInitialHost Catalyst
open DescentPackedEpochShelves DescentPackedProfileInstall DescentWideSeedFlags DescentExterior
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (v : SeedHeader.Input F) (G : PoweredGadget F) (op : RotorSpec)
  (t f g drift h : ℕ)
local notation "s" => v.width G
local notation "R" => v.schedule.copies
local notation "groups" => v.schedule.groupCount 0
local notation "l" => v.layout G t f g drift h
local notation "pitch" => grain (h/2) G.C
local notation "lo" => selectorBase v.circuit R s h v.steps.length
local notation "top" => endAddress v.circuit l v.hosts groups v.k
local notation "finish" => (DescentDatedSeedStartup.Input.nodeChart l v.k v.hosts groups).seedEnd top
local notation "M" => Primitive.paletteLanes G op s (v.schedule.grainAt G.b v.p 0) h v.k

theorem anchor_le_floor :
    end_ (lo+extent pitch v.steps) G.C pitch +
      17*DescentExteriorShelf.span v.j v.rest s (ExteriorCount v.circuit) +
      DescentTerminalPublicIdentity.total v.appendix.bins v.appendix.binWidth v.appendix.arity
        v.appendix.piece v.appendix.codes v.appendix.raw (ExteriorCount v.circuit*2^(v.j+v.rest)) ≤
      v.floor G op t f g drift h := by
  exact (v.header_after_votes G h).1.trans ((Nat.sub_le ..).trans (v.base_le_floor G op t f g drift h))

end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

end OAI
