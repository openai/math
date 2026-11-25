import OAI.Computability.BorderVNP.ShortenEpochRoundRecordEquiv
import OAI.Computability.BorderVNP.ShortenExecutedEpoch

/-!
# Record fields on the original enumeration of a site execution

Run the actual inherited record maps through the same selected physical
program and transport them back along the bijection of attained histograms.
Each ordinal of the ordinary flat tensor expansion receives its own retained
prior and payload maps, with one factor uniform over the cover level and all
input fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SiteExecution

open BorderVNP.Crossing BorderVNP.Cover BorderVNP.Epoch BorderVNP.Epoch.Round Adaptive
open scoped Classical BorderVNP.Epoch.Cube

attribute [local instance] portFintype

variable {D m b k : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} [Fintype P] {bits : P → ℕ}
  {e : PaidIdentity K D m} {h H ν : ℝ} {path : StagePath b e (Cube D) h H ν} {C : Fin b → ℕ}
  {last high : ℕ} {hk : 0 < k} {machine : SiteMachine path C last high hk P bits}
  {low : ℕ} {L weight E A Cout : ℝ} {hh : 0 < h} {cap : ℕ}
  {input : Fin (k^b) → Pack D P bits K} {route : ∀ i, SiteRoutes (input i) (Cube D) high L}
  (run : SiteExecution (low := low) machine hh input route weight E A Cout cap)

/-- Input records on the actual site pack supplied to subdivision. -/
def originalData (fields : ∀ i, RecordData (input i).layout) (i : Fin (k^b)) :
    RecordData (run.initialSites i).pack.layout :=
  cast (congrArg (fun p : Pack D P bits K => RecordData p.layout) (run.originalPack i).symm) (fields i)

/-- Record-carrying leaves corresponding to the actual original input occurrences. -/
noncomputable def recordLeaves (fields : ∀ i, RecordData (input i).layout) :=
  Program.trackedLeaves (view := fun j (p : path.State P bits k last high j) => p.val) run.flat run.initialSites (run.originalData fields)

/-- The exact original-to-decorated ordinal correspondence for this input execution. -/
noncomputable def recordMatch (fields : ∀ i, RecordData (input i).layout) :=
  machine.F.matchRecords machine.stored b le_rfl run.flat (run.recordLeaves fields) (fun _ => rfl)

/-- Retained fields on the original, unflattened network at a specified true terminal profile. -/
noncomputable def terminalRecords (fields : ∀ i, RecordData (input i).layout) (i : machine.F.Hist run.flat) :
    RecordData (machine.F.terminal run.flat i).pack.layout :=
  let G := machine.F.withRecords machine.stored
  let leaf := run.recordLeaves fields
  let r := run.recordMatch fields
  let z := (G.system.histories b le_rfl (leavesEquiv k _ b leaf)).term (r.index i)
  transferData (machine.F.terminal_match machine.stored r i) (machine.F.historyRecords machine.stored b z)

/-- Concrete inherited histories and payloads on the original flat summand indexed by `j`. -/
noncomputable def expansionRecords (fields : ∀ i, RecordData (input i).layout) (j : Fin run.expansion.terms) :
    RecordData (run.expansion.pack j).layout :=
  ⟨(run.terminalRecords fields (run.enum j)).prior,(run.terminalRecords fields (run.enum j)).payload⟩

/-- The exact input metadata meet the same cap on the realized leaf sites. -/
theorem originalData_bound (hdepth : path.depths last high 0 = high)
    (fields : ∀ i, RecordData (input i).layout) (ex : Bool) (M : ℕ)
    (hm : ∀ i t, localRecords (input i).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove high ((route i).origin v) = t) ≤ M) :
    ∀ i t, @localRecords D (Port k P 0) (portFintype (P := P)) (width bits k 0) (run.initialSites i).pack.layout
      ex (run.originalData fields i).prior (run.originalData fields i).payload
      (fun v => reduceMove (path.depths last high 0) ((run.initialSites i).routes.origin v) = t) ≤ M := by
  intro i
  exact RecordData.transfer_site_cap hdepth (run.originalPack i) (run.originalRoutes i) (fields i) ex M
    (fun t => by
      have heq : (portFintype (P := P) (k := k) (b := 0) : Fintype P) = ‹Fintype P› := Subsingleton.elim _ _
      change @localRecords D P (portFintype (P := P) (k := k) (b := 0)) bits (input i).layout ex
        (fields i).prior (fields i).payload (fun v => reduceMove high ((route i).origin v) = t) ≤ M
      rw [heq]; exact hm i t)

set_option maxHeartbeats 2500000 in
/-- The actual retained records of every original expansion summand obey the single
schedule-dependent cap, for each counting mode and for arbitrary input metadata. -/
theorem expansionRecords_bound (hdepth : path.depths last high 0 = high)
    (fields : ∀ i, RecordData (input i).layout) (ex : Bool) (M : ℕ)
    (hm : ∀ i t, localRecords (input i).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove high ((route i).origin v) = t) ≤ M) :
    ∀ (j : Fin run.expansion.terms) t,
      1+localRecords (run.expansion.pack j).layout ex (run.expansionRecords fields j).prior
        (run.expansionRecords fields j).payload (fun v => reduceMove low ((run.expansion.routes j).origin v) = t) ≤
        epochRecordFactor (Cube D) L h (fun u => C u*k) cap*(1+M) := by
  let G := machine.F.withRecords machine.stored
  let leaf := run.recordLeaves fields
  let data := machine.F.historyRecords machine.stored
  let R := run.recordMatch fields
  have start (i : Fin (k^b)) : data 0 (leaf i) = (run.initialSites i).installedData (run.originalData fields i) := rfl
  have initial := run.originalData_bound hdepth fields ex M hm
  have step := machine.F.historyRecords_step machine.stored hk C machine.records ex
  have all := record_tree G leaf run.initialSites (run.originalData fields) data start ex M initial (fun u => C u*k) step
  let B := 1+∑ u, C u*k
  let init := (1+3*Fintype.card (Option (allowedMoves (Cube D) L) × Fin (hopCount L h)))*(1+M)
  have hT : 0 < B^b*init := by dsimp only [B,init]; positivity
  intro j t
  let i := run.enum j
  let z := (G.system.histories b le_rfl (leavesEquiv k _ b leaf)).term (R.index i)
  have hz := G.system.fromInputs_histories (fun a => a ∈ Set.range leaf) b le_rfl
    (leavesEquiv k _ b leaf) (allLeaves_of_flat _ b leaf (fun u => ⟨u,rfl⟩)) (R.index i)
  have hc : RecordsWithin (machine.F.terminal run.flat i) (run.terminalRecords fields i) ex (B^b*init) :=
    (recordsWithin_transfer (machine.F.terminal_match machine.stored R i) (data b z) ex (B^b*init)).mpr
      (all b le_rfl z hz)
  have bound := flat_output_record_bound (machine.F.terminal run.flat i) (run.out i)
    (run.terminalRecords fields i) ex hT hc t
  apply bound.trans_eq
  unfold epochRecordFactor
  dsimp only [B,init]
  ring

end Shortening.SiteExecution

namespace Shortening.SiteSchedule

open BorderVNP.Crossing BorderVNP.Cover BorderVNP.Epoch BorderVNP.Epoch.Round Adaptive
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The per-tile multiplier of the fixed site schedule, independent of the execution,
the cover depth, the external slots and the original pack fields. -/
noncomputable def recordFactor : ℕ := epochRecordFactor (Cube D) S.budget S.radius
  (fun i => S.factors i*S.fanIn) S.finalCap

/-- The level of the first physical stage is the prescribed input level of this schedule. -/
theorem depths_inputLevel (d : ℕ) : S.path.depths S.last (S.inputLevel d) 0 = S.inputLevel d := by
  unfold Adaptive.StagePath.depths
  rw [Levels.start]
  unfold inputLevel drop
  omega

/-- The actual schedule's record certificate on its original enumeration of all the flat
site summands. Both descriptor and expanded bounds use the identical input field maps,
record factor and histogram-to-layout assignment. -/
theorem recordCertificate {d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {Mch : S.Machine d P bits}
    {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
    {route : ∀ i, SiteRoutes (input i) (Cube D) (S.inputLevel d) S.budget} (run : S.Execution Mch input route)
    (fields : ∀ i, RecordData (input i).layout) (ex : Bool) (M : ℕ)
    (hm : ∀ i t, localRecords (input i).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove (S.inputLevel d) ((route i).origin v) = t) ≤ M) :
    ∀ (j : Fin run.expansion.terms) t, 1+localRecords (run.expansion.pack j).layout ex
      (run.expansionRecords fields j).prior (run.expansionRecords fields j).payload
      (fun v => reduceMove (d+1) ((run.expansion.routes j).origin v) = t) ≤ S.recordFactor*(1+M) := by
  exact run.expansionRecords_bound (S.depths_inputLevel d) fields ex M hm

end Shortening.SiteSchedule

end BorderVNP
end Computability
end OAI
