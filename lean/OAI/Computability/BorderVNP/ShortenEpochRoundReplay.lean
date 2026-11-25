import OAI.Computability.BorderVNP.ShortenEpochRoundTrackedRecords

/-!
# Replaying the per-tile bound with arbitrary actual input records

Attach each original record field separately at its particular flat leaf.
The measured program operates on precisely these fields and installs each
histogram's sewn records. Its stage factors are those of the originally
selected steps, multiplied by the fixed fan-in.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive.Program

open BorderVNP.Crossing BorderVNP.Cover BorderVNP.Epoch BorderVNP.Epoch.Round
open scoped Classical

attribute [local instance] portFintype

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I] [Fintype P] {bits : P → ℕ}
  {states : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
  {view : ∀ j, states j → PlacedPack D (Port k P j) (width bits k j) K I (depth j)}
  {e : PaidIdentity K D m} (F : Program (B := B) e view)

/-- Install the indicated input priors and payloads individually at all original flat leaves. -/
def trackedLeaves {L δ : ℝ} {hδ : 0 < δ} (flat : Fin (k^b) → states 0)
    (sites : ∀ i, InitialSites (view 0 (flat i)) L hδ) (input : ∀ i, RecordData (sites i).pack.layout) :
    Fin (k^b) → Tracked view 0 := fun i => ⟨flat i,(sites i).installedData (input i)⟩

set_option maxHeartbeats 2000000 in
/-- Both per-tile record assertions on the same physical histograms, with the per-stage
hypothesis exactly the record certificate supplied by the chosen program. -/
theorem replayed_record_bounds (direct : F.Direct) (hk : 0 < k) (C : Fin b → ℕ)
    (cert : ∀ i c, (F.step i c).RecordFactor e (C i)) {d : ℕ} {L δ A Cout : ℝ} {H : ℕ} {hδ : 0 < δ}
    (flat : Fin (k^b) → states 0) (sites : ∀ i, InitialSites (view 0 (flat i)) L hδ)
    (input : ∀ i, RecordData (sites i).pack.layout) (ex : Bool) (M : ℕ)
    (hM : ∀ i t, localRecords (sites i).pack.layout ex (input i).prior (input i).payload
      (fun v => reduceMove (depth 0) ((sites i).routes.origin v) = t) ≤ M) :
    let G := F.withRecords direct
    let leaf := trackedLeaves flat sites input
    let factor := epochRecordFactor I L δ (fun j => C j*k) H
    ∀ (out : ∀ i : G.Hist leaf, SiteOutput (G.terminal leaf i) d L A Cout H),
      (∀ j ≤ b, ∀ z : (G.system.layer j).Name, G.system.fromInputs (fun x => x ∈ Set.range leaf) j z →
        RecordsWithin (G.executed j z) (F.historyRecords direct j z) ex (factor*(1+M))) ∧
      ∀ i : G.Hist leaf,
        let z := (G.system.histories b le_rfl (leavesEquiv k (Tracked view 0) b leaf)).term i
        let r := F.historyRecords direct b z
        ∀ t, 1+localRecords (flattenPack b (G.terminal leaf i).pack).layout ex r.prior r.payload
          (fun v => reduceMove d ((out i).routes.flatten.origin v) = t) ≤ factor*(1+M) := by
  intro G leaf factor out
  apply epoch_record_bounds G leaf sites input (F.historyRecords direct) _ ex M hM (fun j => C j*k) _ out
  · intro i
    rfl
  · exact F.historyRecords_step direct hk C cert ex

end Shortening.Adaptive.Program

end BorderVNP
end Computability
end OAI
