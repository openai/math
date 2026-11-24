import OAI.Computability.VPVNP.PairRefreshOriginLevelView
import OAI.Computability.VPVNP.PairRefreshHookOrigin

/-! # Successful local tapes at a chronological refresh output

Reindexing the genuine port's placed argument and local occurrence identifies
the accepted suffixes with the term at the indexed output, including for
arbitrary independent half values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM PrivateRAM Compression CompressorRecords PortRefresh LocalHistory NodeArguments
open TraversalRows TraversalRoles ShrinkRoleDirectory NetworkKernel DFS TreeDecode
open PortRefresh.NewSlots
open scoped Fin.CommRing
set_option quotPrecheck false

variable {k K : Type} [_root_.Field k] [CommRing K] {S : BlockSchedule k} {B : S.Templates}
  {f : B.Entry → K} {hf : B.IsSolution f}
  (n hist w start positions blocks width : ℕ) (leaf : TaggedLayer)
  (passes : List (SelectedLevel B f hf))
  (room : Rooms n hist w start positions blocks leaf passes)
  (order : B.Entry ≃ Fin hist) (pub : Fin 11 → Word w) (m : Memory w)
  (x : Row passes)

local notation "v₀" => passes.get x.val.1
local notation "u₀" => Sigma.snd (Subtype.val x)
local notation "r₀" => originReader B f hf (SelectedLevel.origin (v₀)) (SelectedLevel.term (v₀))
local notation "R₀" => rowSite n hist w start positions blocks width leaf passes room x
local notation "ties₀" => RefreshBlockPlan.order B
local notation "stride₀" => LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)

set_option maxHeartbeats 2000000 in
-- Reindexing dependent witnesses unfolds the selected term and its native port.
theorem local_tape_iff
    (z : (passes[x.val.1].pass.step.term passes[x.val.1].term).output.Half x.val.2)
    (s : Scratch w n) (bits tail : List Bool) (hw : 0 < w)
    (stored : (Packet.mk (R₀).parent (packed (R₀).nextState (R₀).newerSite
      (halfEquiv (v₀) (u₀) x.property z))).Stored (R₀).arena s) :
    (∃ body, ((R₀).hook (ties₀) (stride₀) order pub m).read (word (R₀).parent) s bits =
      some (body, tail)) ↔
    ∃ a : Placed ((v₀).pass.step.term (v₀).term).place (v₀).input.network.Half (u₀),
      ∃ c : ((r₀).witness (u₀) a z).Choice, bits = (r₀).nodeBits (u₀) a z c ++ tail := by
  let native := choiceEquiv (v₀) (u₀) x.property z
  let new := halfEquiv (v₀) (u₀) x.property z
  have hp := RefreshHalfDecoder.parent_eq (R₀).nextState (R₀).newerSite (R₀).arena
    (R₀).parent s new stored hw
  rw [(R₀).origin_tape_iff (ties₀) (stride₀) order pub m f hf _ s bits tail new hp]
  constructor
  · rintro ⟨a, c, eqn⟩
    let occ := native.symm ⟨a, c⟩
    refine ⟨occ.1, occ.2, ?_⟩
    have same := (choice_fields (v₀) (u₀) x.property z occ.1 occ.2).2.1
    change (r₀).nodeBits (u₀) occ.1 z occ.2 =
      (originReader B f hf (PassOrigin.refresh (R₀).state) (R₀).choice).nodeBits (R₀).newerSite
        (native occ).1 new (native occ).2 at same
    rw [show native occ = ⟨a, c⟩ from native.apply_symm_apply _] at same
    exact eqn.trans (congrArg (· ++ tail) same.symm)
  · rintro ⟨a, c, eqn⟩
    let occ := native ⟨a, c⟩
    exact ⟨occ.1, occ.2,
      eqn.trans (congrArg (· ++ tail) (choice_fields (v₀) (u₀) x.property z a c).2.1)⟩

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
