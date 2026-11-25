import OAI.Hierarchy.DescentRegisteredSeedGeometry
import OAI.Hierarchy.DescentRegisteredProfileMenu
import OAI.Hierarchy.DescentDateLaneAmount

namespace OAI
/-! # Initial register geometry for the numbered ballot shelves -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedSeedStartup DescentSIMDLookup DescentTerminalEpochChart DescentPackedEpochShelves
noncomputable section
set_option quotPrecheck false
variable {A F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n D cp nP : ℕ}
  (board : NonlinearExpanders.Graph n D) (op : RotorSpec)
  (k tail p f gain drift degree payload lo hdr : ℕ) (entries : List (Source A))
  (X : Catalyst.Approximation F cp nP) (R base wire hist H w : ℕ)
local notation "b" => fromProfiles G S board op k tail p f gain drift degree payload lo hdr entries
local notation "groups" => S.groupCount 0
local notation "layout" => selectedLayout G S payload k tail gain p drift degree f (quota S.rounds) base (S.censusBits p) wire hist
local notation "Z" => S.grainAt G.b p 0
local notation "pos" => DatePorts.initial G op X R layout k H groups payload Z
local notation "top" => DescentDatedSeedStartup.endAddress X layout H groups k
local notation "done" => (Input.nodeChart layout k H groups).seedEnd top
local notation "M" => Primitive.paletteLanes G op (layout).seedWidth Z payload k
local notation "floor" => Primitive.initialEnd X R (layout).seedWidth payload k H groups M done

theorem profiled_seed_geometry (epochs : 0<S.height) (branch : G.b≤2^S.capGain) (radix : S.radix=2^k)
    (sites : ∃d,S.initialSites=2^d) (scheduled : ∃t reset J N,S=stageNumbers G t J f gain reset N tail)
    (old : S.hostSize 0≤H) (bounded : H≤DescentCompiler.TerminalScale.hostRows (S.hostSize 0))
    (space : floor<2^w) : Geometry G S b k w 0 ⟨pos,floor⟩ :=
  original_seed_geometry G S b X R k base wire hist H w (fun _=>DonorDate.seed_lanes G S gain k p payload)
    epochs branch radix sites scheduled old bounded space

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
