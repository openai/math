import OAI.Computability.VPVNP.PairRefreshHookWitness
import OAI.Computability.VPVNP.PairRefreshTraversalOriginBits
import OAI.Computability.VPVNP.PairTreeNodeReaders

/-! # Equality of the refresh hook and the selected term reader on suffixes

The physical row and the mathematical term both consume the sole placed
child's half. The successful kernel witness consumes the empty word. These
equalities characterize every accepted suffix, including an empty child.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords CompressorRecords.PortRefresh NewSlots NodeArguments NodeArguments.ChildScan
open LocalHistory VertexImage DFS NetworkKernel

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {bits n hist t : ℕ}
  (R : Site B n hist bits) (ties : Fin t ≃ Tie (2^S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (pub : Fin 11 → BurstRAM.Word bits) (m : Memory bits)
variable {K : Type*} [CommRing K] (f : B.Entry → K) (hf : B.IsSolution f)
local notation "reader" => originReader B f hf (PassOrigin.refresh R.state) R.choice
local notation "site" => R.newerSite

set_option maxHeartbeats 1200000 in
/-- Every complete physical local prefix is the corresponding term
reader's own word, and every such term word is consumed on the real row. -/
theorem origin_tape_iff (node : BurstRAM.Word bits) (s : Scratch bits n) (bs tail : List Bool)
    (new : R.nextState.network.Half site)
    (hp : RefreshHalfDecoder.parent R.nextState site R.arena R.parent s = some new) :
    (∃ job, (R.hook ties stride order pub m).read node s bs = some (job,tail)) ↔
      ∃ before, ∃ w : ((reader).witness site before new).Choice, bs = (reader).nodeBits site before new w ++ tail := by
  rw [R.hook_witness_iff ties stride order pub m f hf node s bs tail new hp]
  constructor
  · rintro ⟨before,tape,⟨w⟩⟩
    refine ⟨before,w,?_⟩
    rw [TraversalPlan.origin_nodeBits B f hf R.state R.choice R.port before new w]
    exact tape
  · rintro ⟨before,w,tape⟩
    refine ⟨before,?_,⟨w⟩⟩
    rwa [TraversalPlan.origin_nodeBits B f hf R.state R.choice R.port before new w] at tape

private theorem map_snd_eq {α : Type*} (value : Option (α × List Bool)) (tail : List Bool) :
    value.map Prod.snd = some tail ↔ ∃ x, value = some (x,tail) := by
  cases value with
  | none => simp
  | some pair => cases pair; simp

set_option maxHeartbeats 1200000 in
/-- Equality of the actual and semantic unconsumed streams. A rejection
by either parser excludes every returned suffix. -/
theorem origin_suffix (node : BurstRAM.Word bits) (s : Scratch bits n) (bs : List Bool)
    (new : R.nextState.network.Half site)
    (hp : RefreshHalfDecoder.parent R.nextState site R.arena R.parent s = some new) :
    ((R.hook ties stride order pub m).read node s bs).map Prod.snd =
      ((TreeDecode.nodeReader (reader) site new).read bs).map Prod.snd := by
  let native := (R.hook ties stride order pub m).read node s bs
  let C := TreeDecode.nodeReader (reader) site new
  have test (tail : List Bool) : native.map Prod.snd = some tail ↔ (C.read bs).map Prod.snd = some tail := by
    rw [map_snd_eq native tail,map_snd_eq (C.read bs) tail]
    rw [R.origin_tape_iff ties stride order pub m f hf node s bs tail new hp]
    constructor
    · rintro ⟨before,w,tape⟩
      exact ⟨⟨before,w⟩,(C.read_iff bs ⟨before,w⟩ tail).mpr tape⟩
    · rintro ⟨⟨before,w⟩,hit⟩
      exact ⟨before,w,(C.read_iff bs ⟨before,w⟩ tail).mp hit⟩
  change native.map Prod.snd = (C.read bs).map Prod.snd
  cases h : (C.read bs).map Prod.snd with
  | some tail => exact (test tail).mpr h
  | none =>
    cases p : native.map Prod.snd with
    | none => rfl
    | some tail =>
      have impossible := (test tail).mp p
      rw [h] at impossible
      cases impossible

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
