import OAI.Hierarchy.DescentRegisteredSeedRooms
import OAI.Hierarchy.DescentRegisteredGeometry

namespace OAI
/-! # All three original bank families at the first native instruction -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedSeedStartup DescentSIMDLookup
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n degree cp nP : ℕ}
  (b : Menu n degree) (X : Catalyst.Approximation F cp nP)
  (R k base wire hist H w : ℕ)
local notation "groups" => S.groupCount 0
local notation "field" => S.censusBits b.p
local notation "layout" => selectedLayout G S b.payload k b.tail b.gain b.p b.drift b.degreeLimit b.f
  (quota S.rounds) base field wire hist
local notation "Z" => S.grainAt G.b b.p 0
local notation "register" => DatePorts.initial G b.op X R layout k H groups b.payload Z
local notation "top" => DescentDatedSeedStartup.endAddress X layout H groups k
local notation "chart" => Input.nodeChart layout k H groups
local notation "stopped" => (chart).seedEnd top
local notation "M" => Primitive.paletteLanes G b.op (layout).seedWidth Z b.payload k
local notation "floor" => Primitive.initialEnd X R (layout).seedWidth b.payload k H groups M stopped

theorem original_seed_geometry (first : S.rounds≠0 → (b.ordinary 0).lanesAt=lanes b.payload (firstDonor G S b.gain k b.p))
    (epochs : 0<S.height) (branch : G.b≤2^S.capGain) (radix : S.radix=2^k)
    (sites : ∃d,S.initialSites=2^d) (scheduled : ∃t reset J N,S=stageNumbers G t J b.f b.gain reset N b.tail)
    (old : S.hostSize 0≤H) (bounded : H≤DescentCompiler.TerminalScale.hostRows (S.hostSize 0))
    (space : floor<2^w) : Geometry G S b k w 0 ⟨register,floor⟩ :=by
  have nodeRoom : top≤ stopped := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  obtain ⟨source,issued⟩:=Primitive.fences X R (layout).seedWidth b.payload k H groups M stopped
  exact ⟨DatePorts.initial_archive_fits G b.op X R layout k H groups b.payload Z,
    initial_register_room G S b X R k (quota S.rounds) base field wire hist H groups floor w
      epochs branch radix sites scheduled old bounded rfl ((nodeRoom.trans source).trans issued) space,
    seed_venue_format (G:=G) (S:=S) (k:=k) b X R H groups base wire hist Z floor first,rfl,
    by simp only [Nat.zero_mod,atRound]; rfl,
    by simp only [List.take_zero,List.prod_nil,Nat.one_mul]; rfl⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
