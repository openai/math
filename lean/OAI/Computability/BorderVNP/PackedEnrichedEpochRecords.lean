import OAI.Computability.BorderVNP.PackedHistoryNormalizedEnriched
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseExecutionRecords

/-! # Physical records on the richer named processor state

The true machine keeps its incoming cable order, outgoing cable order and
auxiliary words throughout each inner history. Its stage measurements and
retained records apply to that exact geometric view of the named state.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SiteSchedule.EnrichedExecution

open Crossing Epoch Epoch.Round Cover Shortening Packing Catalog Adaptive
open scoped Classical
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {A : ℕ → Type*} {view : S.GeometricView d P bits A} {F : S.EnrichedProgram d view}
    {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
    {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget} (run : EnrichedExecution F input route)
    (fields : ∀ i, RecordData (input i).layout)

/-- Input box fields transported to the very input installed at this leaf. -/
def inputFields (i : Fin (S.fanIn^S.rounds)) : RecordData (run.initialSites i).pack.layout :=
  cast (congrArg (fun p : Pack D P bits K => RecordData p.layout) (run.originalPack i).symm) (fields i)

/-- The corresponding initial local bounds hold at the real input cover depth. -/
theorem inputFields_bound (ex : Bool) (M : ℕ)
    (hm : ∀ i t, localRecords (input i).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove (S.high d) ((route i).origin v) = t) ≤ M) :
    ∀ i t, @localRecords D (Port S.fanIn P 0) (portFintype (P := P)) (width bits S.fanIn 0)
      (run.initialSites i).pack.layout ex (run.inputFields fields i).prior (run.inputFields fields i).payload
      (fun v => reduceMove (S.level d 0) ((run.initialSites i).routes.origin v) = t) ≤ M := by
  intro i
  exact RecordData.transfer_site_cap (S.start_level d) (run.originalPack i) (run.originalRoutes i) (fields i) ex M
    (fun t => by
      have heq : (portFintype (P := P) (k := S.fanIn) (b := 0) : Fintype P) = ‹Fintype P› := Subsingleton.elim _ _
      change @localRecords D P (portFintype (P := P) (k := S.fanIn) (b := 0)) bits (input i).layout ex
        (fields i).prior (fields i).payload (fun v => reduceMove (S.high d) ((route i).origin v) = t) ≤ M
      rw [heq]; exact hm i t)

/-- The installed metadata in the selected output of this native histogram. -/
noncomputable def recordFields (names : F.SaveNames) (q : F.Hist run.flat) :
    RecordData (flattenPack S.rounds (F.terminal run.flat q).pack).layout :=
  let r := F.siteRecords names run.flat run.initialSites (run.inputFields fields) q
  ⟨r.prior,r.payload⟩

/-- Both modes of the local cap use the same named histories and the same
public terminal motions, including when child sidecar fields differ. -/
theorem recordCertificate (names : F.SaveNames)
    (cert : ∀ i c, (F.stage i c).RecordFactor e (S.source.pattern i).record) (ex : Bool) (M : ℕ)
    (hm : ∀ i t, localRecords (input i).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove (S.high d) ((route i).origin v) = t) ≤ M) :
    ∀ q t, 1+localRecords (flattenPack S.rounds (F.terminal run.flat q).pack).layout ex
      (run.recordFields fields names q).prior (run.recordFields fields names q).payload
      (fun v => reduceMove (d+1) ((run.output.out q).routes.flatten.origin v) = t) ≤ S.recordFactor*(1+M) :=
  fun q t => F.siteRecords_bound names (fun i => (S.source.pattern i).record) cert
    run.flat run.initialSites (run.inputFields fields) ex M (run.inputFields_bound fields ex M hm) q (run.output.out q) t

end PackedHistoryCircuit.Normalized.SiteSchedule.EnrichedExecution

end BorderVNP
end Computability
end OAI
