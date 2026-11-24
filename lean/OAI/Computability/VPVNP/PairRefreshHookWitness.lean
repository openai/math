import OAI.Computability.VPVNP.PairRefreshHookSite
import OAI.Computability.VPVNP.PairRefreshTraversalWitness

/-!
# Accepted physical refresh tapes and scheduled kernel witnesses

At a fixed prepared node the newer argument is determined by the resident
packet. The old half occurs once on the private choice tape. Every accepted
suffix corresponds to a placed old argument with a genuine dyadic kernel
witness, including when a selected scalar vanishes in the coefficient field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords CompressorRecords.PortRefresh NewSlots NodeArguments NodeArguments.ChildScan
open VertexImage DFS NetworkKernel

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {bits n hist t : ℕ}
  (R : Site B n hist bits) (ties : Fin t ≃ Tie (2^S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (pub : Fin 11 → BurstRAM.Word bits) (m : Memory bits)

local notation "X" => R.state
local notation "Y" => R.nextState
local notation "oldSite" => R.olderSite
local notation "newSite" => R.newerSite

/-- Recover the independently guessed half and the acceptance bit of the
actual finite refresh map from the physical parser. -/
theorem hook_choice_iff (node : BurstRAM.Word bits) (s : Scratch bits n) (bs tail : List Bool)
    (new : (Y).network.Half newSite)
    (hp : RefreshHalfDecoder.parent Y newSite R.arena R.parent s = some new) :
    (∃ job, (R.hook ties stride order pub m).read node s bs = some (job,tail)) ↔
    ∃ old : (X).network.Half oldSite, bs = packed X oldSite old ++ tail ∧
      (TraversalPlan.emitted B order X R.choice R.port old new).isSome = true := by
  constructor
  · rintro ⟨job,h⟩
    obtain ⟨⟨out,rest⟩,hr,hj⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨_,rfl⟩ := Prod.mk.inj hj
    obtain ⟨parent,tape,es,action,_⟩ := (RefreshHook.read_some_iff X oldSite Y newSite R.arena R.oldNode R.parent
      (R.front pub m) (R.action ties stride order pub m) node s bs out rest).mp hr
    obtain rfl := Option.some.inj (hp.symm.trans parent)
    refine ⟨out.value.1,tape,?_⟩
    unfold Site.action TraversalPlan.canonicalAction at action
    split at action
    · assumption
    · contradiction
  · rintro ⟨old,tape,accepted⟩
    have hh := (RefreshHalfDecoder.read_iff X oldSite bs old tail).mpr tape
    simp [Site.hook,ShrinkRole.hook,Site.read,RefreshHook.reader,hp,hh,Site.action,TraversalPlan.canonicalAction,accepted]

variable {K : Type*} [CommRing K] (f : B.Entry → K) (hf : B.IsSolution f)
local notation "place₀" => TraversalPlan.place X
local notation "v" => R.port
local notation "conn" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hsol" => And.right (Iff.mp (B.solution_iff f) hf)

/-- The physical accepted old-half prefixes are precisely the assigned inputs
of the selected dyadic kernel that have a monomial witness. -/
theorem hook_witness_iff (node : BurstRAM.Word bits) (s : Scratch bits n) (bs tail : List Bool)
    (new : (Y).network.Half newSite)
    (hp : RefreshHalfDecoder.parent Y newSite R.arena R.parent s = some new) :
    (∃ job, (R.hook ties stride order pub m).read node s bs = some (job,tail)) ↔
    ∃ before : Placed place₀ (X).network.Half newSite,
      bs = packed X oldSite (before oldSite (TraversalPlan.old_place X v)) ++ tail ∧
      Nonempty (dyadicRefreshKernelWitness X S.graph (Nat.two_pow_pos _) conn B.refresh
        S.port_order S.degree_bounds.2 (f ∘ Sum.inr) hsol R.choice newSite before new).Choice := by
  rw [R.hook_choice_iff ties stride order pub m node s bs tail new hp]
  constructor
  · rintro ⟨old,tape,accept⟩
    let before := TraversalPlan.placedHalf X v old
    have same : before oldSite (TraversalPlan.old_place X v) = old := rfl
    refine ⟨before,same ▸ tape,?_⟩
    exact (TraversalPlan.emitted_iff_witness B order X R.choice v new before f hf).mp (same ▸ accept)
  · rintro ⟨before,tape,witness⟩
    exact ⟨_,tape,(TraversalPlan.emitted_iff_witness B order X R.choice v new before f hf).mpr witness⟩

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
