import OAI.Hierarchy.DescentPhysicalTrunkBanks

namespace OAI
/-! # The full reset peer, parent, stem, and compact trunk publication -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (v : CandidateFront) (floor : ℕ) (s : v.Scene) {w : ℕ} (space : v.SceneRoom floor s w)
local notation "first₀" => v.received floor s space
local notation "finish₀" => DescentResetTrunkCompactProgram.phase w (v.mixed floor) v.newHosts v.peer.hosts
  v.peer.groups v.peer.lanes v.metaBits (v.trunkBanks floor s)

def trunkScene : NativePhase w := (first₀).seq finish₀

theorem trunkScene_any (m : Memory w) (room : v.trunkEnd floor<2^w) :
    (v.trunkScene floor s space).Runs m ∧
    ∀a,a<floor ∨ v.trunkEnd floor≤a→(v.trunkScene floor s space).image m a=m a := by
  have early:=v.received_any floor s space m
  have rest:=v.trunk_any floor s space ((first₀).image m) room
  have start:=v.received_start floor s space
  have end_ : v.mixed floor≤v.trunkEnd floor :=
    (DescentResetTrunkCompactProgram.grow ..).trans (Nat.le_add_right ..)
  refine ⟨(first₀).seq_runs finish₀ m early.1 rest.1,?_⟩
  intro a out
  exact (rest.2 a (out.imp_left (·.trans_le start))).trans (early.2 a (out.imp_right (end_.trans ·)))

theorem trunkScene_before (m : Memory w) (room : v.trunkEnd floor<2^w) (a : ℕ) (old : a<v.mixed floor) :
    (v.trunkScene floor s space).image m a=(first₀).image m a :=
  (v.trunk_any floor s space ((first₀).image m) room).2 a (.inl old)

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
