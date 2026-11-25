import OAI.Computability.BorderVNP.ShortenDenseExecution
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseSiteRecords

/-!
# Record certificates on the actual publicly normalized site execution

The fixed source path contributes the record factor of each selected dense
physical stage. The machine contributes the concrete destination numbering
of each true histogram. Both per-tile assertions are evaluated on those
same physical states, with the original leaf records supplied independently
at each occurrence.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open BorderVNP.Cover BorderVNP.Crossing BorderVNP.Shortening BorderVNP.Epoch BorderVNP.Epoch.Round
open BorderVNP.Shortening.Adaptive
open scoped Classical BorderVNP.Epoch.Cube

attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}

namespace SiteSchedule

/-- Uniform per-tile record multiplier fixed before the layout, level, field entries or ordinal. -/
noncomputable def recordFactor (S : SiteSchedule e) :=
  epochRecordFactor (Cube D) S.budget S.radius (fun i => (S.source.pattern i).record*S.fanIn) S.finalCap

/-- The input stage occupies exactly the prescribed higher congruence level. -/
theorem start_level (S : SiteSchedule e) (d : ℕ) : S.level d 0 = S.high d := by
  let w := fun i => (S.source.pattern i).word
  change Levels.level w (S.high d-S.drop) S.last 0 = _
  rw [Levels.start]
  change S.high d-S.drop+S.drop = S.high d
  unfold high
  omega

end SiteSchedule

namespace SiteExecution

variable {S : SiteSchedule e} {d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {Mch : SiteMachine S d P bits}
  {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
  {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}
  (run : SiteExecution S Mch input route)

/-- The original input record maps on the actual site network passed to the subdivision. -/
def inputFields (fields : ∀ i, RecordData (input i).layout) (i : Fin (S.fanIn^S.rounds)) :
    RecordData (run.initialSites i).pack.layout :=
  cast (congrArg (fun p : Pack D P bits K => RecordData p.layout) (run.originalPack i).symm) (fields i)

/-- The real record maps installed on the ordinary flat network of this original histogram ordinal. -/
noncomputable def recordFields (fields : ∀ i, RecordData (input i).layout) (q : Mch.F.Hist run.flat) :
    RecordData (flattenPack S.rounds (Mch.F.terminal run.flat q).pack).layout :=
  let r := Mch.F.siteRecords Mch.saveNames run.flat run.initialSites (run.inputFields fields) q
  ⟨r.prior,r.payload⟩

/-- Transfer the stated original per-tile cap through the actual starting route equality. -/
theorem inputFields_bound (fields : ∀ i, RecordData (input i).layout) (ex : Bool) (M : ℕ)
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

/-- Uniform terminal bound on the installed public and expanded fields of the same flat
summands as the exact normalized tensor expansion. -/
theorem recordCertificate (fields : ∀ i, RecordData (input i).layout) (ex : Bool) (M : ℕ)
    (hm : ∀ i t, localRecords (input i).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove (S.high d) ((route i).origin v) = t) ≤ M) :
    ∀ (q : Mch.F.Hist run.flat) t, 1+localRecords (flattenPack S.rounds (Mch.F.terminal run.flat q).pack).layout ex
      (run.recordFields fields q).prior (run.recordFields fields q).payload
      (fun v => reduceMove (d+1) ((run.out q).routes.flatten.origin v) = t) ≤ S.recordFactor*(1+M) := by
  intro q t
  exact Mch.F.siteRecords_bound Mch.saveNames (fun i => (S.source.pattern i).record) Mch.records
    run.flat run.initialSites (run.inputFields fields) ex M (run.inputFields_bound fields ex M hm) q (run.out q) t

/-- The retained fields on the ordinary external-slot layout at the execution's own
enumerated public summand number. -/
noncomputable def expansionRecords (fields : ∀ i, RecordData (input i).layout) (j : Fin run.expansion.terms) :
    RecordData (run.expansion.pack j).layout := run.recordFields fields (run.enum j)

/-- Both record modes obey the fixed multiplier on the same finite enumeration of the
ordinary site packs that appears in the execution's tensor identity. -/
theorem expansionRecords_bound (fields : ∀ i, RecordData (input i).layout) (ex : Bool) (M : ℕ)
    (hm : ∀ i t, localRecords (input i).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove (S.high d) ((route i).origin v) = t) ≤ M) :
    ∀ (j : Fin run.expansion.terms) t, 1+localRecords (run.expansion.pack j).layout ex
      (run.expansionRecords fields j).prior (run.expansionRecords fields j).payload
      (fun v => reduceMove (d+1) ((run.expansion.routes j).origin v) = t) ≤ S.recordFactor*(1+M) :=
  fun j => run.recordCertificate fields ex M hm (run.enum j)

/-- The same cap throughout every original normalized physical subtree, counting the
actual records installed by its selected cuts and second row numberings. -/
theorem intermediateRecordCertificate (fields : ∀ i, RecordData (input i).layout) (ex : Bool) (M : ℕ)
    (hm : ∀ i t, localRecords (input i).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove (S.high d) ((route i).origin v) = t) ≤ M)
    (n : ℕ) (hn : n ≤ S.rounds) (pick : Fin (S.fanIn^n) → Fin (S.fanIn^S.rounds))
    (q : Mch.F.FlatHist n hn (run.flat ∘ pick)) :
    RecordsWithin (Mch.F.flatPack n hn (run.flat ∘ pick) q)
      (Mch.F.replayRecords Mch.saveNames n hn (run.flat ∘ pick)
        (fun i => (run.initialSites (pick i)).installedData (run.inputFields fields (pick i))) q) ex
      (S.recordFactor*(1+M)) :=
  Mch.F.intermediateSiteRecords_bound Mch.saveNames (fun i => (S.source.pattern i).record) Mch.records S.finalCap
    run.flat run.initialSites (run.inputFields fields) ex M (run.inputFields_bound fields ex M hm) n hn pick q

end SiteExecution
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
