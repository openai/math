import OAI.Hierarchy.DescentNamedSeedEntryGeometry
import OAI.Hierarchy.DescentSeedTokenStartup

namespace OAI
/-! The dated profile ends before the chosen header and the original seed banks. -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader.Input
open DescentSixParty DescentCompiler DescentInitialHost DescentSeedRoot Catalyst
open DescentPackedEpochShelves DescentPackedProfileInstall DescentWideSeedFlags DescentExterior
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)
  (t f g drift h : ℕ) (v : SeedHeader.Input F)
local notation "s" => v.width G
local notation "l" => v.layout G t f g drift h
local notation "pitch" => DescentPackedEpochShelves.grain (h/2) G.C
local notation "R" => v.schedule.copies
local notation "groups" => v.schedule.groupCount 0
local notation "lo" => selectorBase v.circuit R s h v.steps.length
local notation "top" => endAddress v.circuit l v.hosts groups v.k
local notation "finish" => (DescentDatedSeedStartup.Input.nodeChart l v.k v.hosts groups).seedEnd top
local notation "M" => Primitive.paletteLanes G op s (v.schedule.grainAt G.b v.p 0) h v.k
local notation "cap" => Primitive.initialEnd v.circuit R s h v.k v.hosts groups M finish

theorem profile_fences : lo+extent pitch v.steps ≤ v.base G h-1 ∧
    v.base G h-1 < (v.position G op t f g drift h).floor :=by
  have early : v.base G h-1 < v.base G h:=by dsimp only [base]; omega
  have first:=fences v.circuit l v.hosts groups v.k
  have booked : v.base G h ≤ top:=first.1.trans (first.2.1.trans first.2.2)
  have nodeEnd : top ≤ finish:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have last:=Primitive.fences v.circuit R s h v.k v.hosts groups M finish
  have physical : finish ≤ cap:=last.1.trans last.2
  constructor
  · dsimp only [base,publicFront,end_,dict]
    omega
  · exact early.trans_le (booked.trans (nodeEnd.trans physical))

end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

end OAI
