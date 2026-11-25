import OAI.Hierarchy.DescentSeedHeaderLayout
import OAI.Hierarchy.DescentSeedRegisterPorts
import OAI.Hierarchy.DescentRegisterTimelineCore

namespace OAI
/-! # The original registered position at the end of initialization -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader.Input
open DescentCompiler DescentSixParty DescentSixParty.Chronology DescentInitialHost Catalyst
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec) (t f g drift : ℕ) (v : SeedHeader.Input F)
def position (h : ℕ) : RegisterTimeline.Position :=
  let l:=v.layout G t f g drift h
  let Z:=v.schedule.grainAt G.b v.p 0
  ⟨DatePorts.initial G op v.circuit v.schedule.copies l v.k v.hosts (v.schedule.groupCount 0) h Z,
    v.floor G op t f g drift h⟩
end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

end OAI
