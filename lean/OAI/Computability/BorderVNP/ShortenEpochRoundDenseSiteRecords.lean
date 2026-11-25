import OAI.Computability.BorderVNP.ShortenEpochRoundDenseReplay
import OAI.Computability.BorderVNP.ShortenDenseSiteHistory

/-!
# Original and returned site records for the normalized dense program

The initial equality subdivision installs records on the actual flat
leaves. Each true dense histogram replays its own normalized steps and
destination saves. Final site rounding and flat port labelling preserve the
per-tile cap with the same fixed factor as in the geometric epoch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open BorderVNP.Crossing BorderVNP.Cover BorderVNP.Epoch BorderVNP.Epoch.Round BorderVNP.Packing
open BorderVNP.Shortening BorderVNP.Shortening.Adaptive Finset
open scoped Classical

attribute [local instance] portFintype

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I] [Fintype P] {bits : P → ℕ}
    {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ j, A j → PlacedPack D (Port k P j) (width bits k j) K I (depth j)}
    (F : Program (B := B) e view)

/-- Actual sewn fields carried by a true dense terminal histogram above the original site leaves. -/
noncomputable def siteRecords (S : F.SaveNames) {L δ : ℝ} {hδ : 0 < δ}
    (flat : Fin (k^b) → A 0) (sites : ∀ i, InitialSites (view 0 (flat i)) L hδ)
    (fields : ∀ i, RecordData (sites i).pack.layout) (q : F.Hist flat) :
    RecordData (F.terminal flat q).pack.layout :=
  F.replayRecords S b le_rfl flat (fun i => (sites i).installedData (fields i)) q

/-- The actual per-tile record certificate on the original terminal dense ordinal, for the
same final site motion as the length estimate and the same row-major flat port relabelling. -/
theorem siteRecords_bound (S : F.SaveNames) (C : Fin b → ℕ)
    (cert : ∀ i c, (F.stage i c).RecordFactor e (C i)) {d : ℕ} {L δ W X : ℝ} {H : ℕ} {hδ : 0 < δ}
    (flat : Fin (k^b) → A 0) (sites : ∀ i, InitialSites (view 0 (flat i)) L hδ)
    (fields : ∀ i, RecordData (sites i).pack.layout) (ex : Bool) (M : ℕ)
    (hin : ∀ i t, localRecords (sites i).pack.layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove (depth 0) ((sites i).routes.origin v) = t) ≤ M)
    (q : F.Hist flat) (out : SiteOutput (F.terminal flat q) d L W X H) :
    let r := F.siteRecords S flat sites fields q
    ∀ t, 1+localRecords (flattenPack b (F.terminal flat q).pack).layout ex r.prior r.payload
        (fun v => reduceMove d (out.routes.flatten.origin v) = t) ≤ epochRecordFactor I L δ (fun i => C i*k) H*(1+M) := by
  intro r t
  let factor := 1+∑ i, C i*k
  let init := (1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L δ)))*(1+M)
  have hinit : 0 < init := by dsimp only [init]; positivity
  have old := fun i => (sites i).installedData_within (fields i) ex M (hin i)
  have replay := F.replayRecords_bound S C cert ex init hinit b le_rfl flat (fun i => (sites i).installedData (fields i)) old q
  have hpos : 0 < factor^b*init := Nat.mul_pos (pow_pos (Nat.add_pos_left (by decide) _) _) hinit
  exact (flat_output_record_bound (F.terminal flat q) out r ex hpos replay t).trans_eq
    (by unfold epochRecordFactor; dsimp only [init,factor]; ring)

/-- Every intermediate normalized physical state has the same bound, for every choice of
a subarray of the original site leaves and every actual public profile of that subtree. -/
theorem intermediateSiteRecords_bound (S : F.SaveNames) (C : Fin b → ℕ)
    (cert : ∀ i c, (F.stage i c).RecordFactor e (C i)) {L δ : ℝ} (H : ℕ) {hδ : 0 < δ}
    (flat : Fin (k^b) → A 0) (sites : ∀ i, InitialSites (view 0 (flat i)) L hδ)
    (fields : ∀ i, RecordData (sites i).pack.layout) (ex : Bool) (M : ℕ)
    (hin : ∀ i t, localRecords (sites i).pack.layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove (depth 0) ((sites i).routes.origin v) = t) ≤ M)
    (n : ℕ) (hn : n ≤ b) (pick : Fin (k^n) → Fin (k^b)) (q : F.FlatHist n hn (flat ∘ pick)) :
    RecordsWithin (F.flatPack n hn (flat ∘ pick) q)
      (F.replayRecords S n hn (flat ∘ pick) (fun i => (sites (pick i)).installedData (fields (pick i))) q)
      ex (epochRecordFactor I L δ (fun i => C i*k) H*(1+M)) := by
  let factor := 1+∑ i, C i*k
  let init := (1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L δ)))*(1+M)
  have hinit : 0 < init := by dsimp only [init]; positivity
  have hf : 0 < factor := Nat.add_pos_left (by decide) _
  have old := fun i => (sites (pick i)).installedData_within (fields (pick i)) ex M (hin (pick i))
  have replay := F.replayRecords_bound S C cert ex init hinit n hn (flat ∘ pick)
    (fun i => (sites (pick i)).installedData (fields (pick i))) old q
  intro t
  apply (replay t).trans
  calc
    factor^n*init ≤ factor^b*init := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hf hn)
    _ ≤ (1+H)*(factor^b*init) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold epochRecordFactor; dsimp only [factor,init]; ring

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
