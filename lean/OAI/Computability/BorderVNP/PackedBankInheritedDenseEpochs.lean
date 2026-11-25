import OAI.Computability.BorderVNP.PackedBankInheritedDenseReplay
import OAI.Computability.BorderVNP.PackedDenseEpochRecords

/-! # Cumulative bank records on complete normalized physical epochs

The measured normalized machine supplies the record factor of each chosen
stage and both public cable orderings. Initial subdivision and final rounding
put its cumulative fields on the actual expansion ordinals and routed sites.
The same per-epoch factor then applies throughout the outer physical tree.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Cover Crossing Shortening Epoch Epoch.Round Shortening.Adaptive Packing.InheritedBank
open scoped Classical Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}

/-- Fixed factor for the cumulative fields after a full normalized site epoch. -/
noncomputable def SiteSchedule.bankRecordFactor (S : SiteSchedule e) :=
  epochRecordFactor (Cube D) S.budget S.radius (fun i => loadMultiplier e*(S.source.pattern i).record*S.fanIn) S.finalCap

namespace SiteExecution

variable {S : SiteSchedule e} {d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {Mch : SiteMachine S d P bits}
  {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
  {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}
  (run : SiteExecution S Mch input route) (fields : ∀ i, RecordData (input i).layout)

/-- Cumulative fields at a given stored histogram over any subarray of the genuine input occurrences. -/
noncomputable def partialBankFields (n : ℕ) (hn : n ≤ S.rounds) (pick : Fin (S.fanIn^n) → Fin (S.fanIn^S.rounds))
    (q : Mch.F.FlatHist n hn (run.flat ∘ pick)) : RecordData (Mch.F.flatPack n hn (run.flat ∘ pick) q).pack.layout :=
  Mch.F.replayBankRecords Mch.saveNames n hn (run.flat ∘ pick)
    (fun i => (run.initialSites (pick i)).installedData (run.inputFields fields (pick i))) q

/-- Every chosen intermediate ordinal inherits the actual subdivided input cap, followed
by one normalized bank multiplier per selected stage. -/
theorem partialBankFields_bound (ex : Bool) (M : ℕ)
    (hm : ∀ i t, localRecords (input i).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove (S.high d) ((route i).origin v) = t) ≤ M)
    (n : ℕ) (hn : n ≤ S.rounds) (pick : Fin (S.fanIn^n) → Fin (S.fanIn^S.rounds))
    (q : Mch.F.FlatHist n hn (run.flat ∘ pick)) :
    RecordsWithin (Mch.F.flatPack n hn (run.flat ∘ pick) q) (run.partialBankFields fields n hn pick q) ex
      ((1+∑ i, loadMultiplier e*(S.source.pattern i).record*S.fanIn)^n *
        ((1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius)))*(1+M))) := by
  have hin := run.inputFields_bound fields ex M hm
  let init := (1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius)))*(1+M)
  exact Mch.F.replayBankRecords_bound Mch.saveNames (fun i => (S.source.pattern i).record) Mch.records ex init
    (by dsimp [init]; positivity) n hn (run.flat ∘ pick)
    (fun i => (run.initialSites (pick i)).installedData (run.inputFields fields (pick i)))
    (fun i => (run.initialSites (pick i)).installedData_within _ ex M (hin (pick i))) q

/-- Cumulative fields of the normalized execution's original flattened summand. -/
noncomputable def expansionBankRecords (j : Fin run.expansion.terms) : RecordData (run.expansion.pack j).layout :=
  let result := run.partialBankFields fields S.rounds le_rfl id (run.enum j)
  ⟨result.prior,result.payload⟩

/-- The flat summand's original ordinal and actual terminal site motion obey the fixed
cumulative bank factor on each routed tile. -/
theorem expansionBankRecords_bound (ex : Bool) (M : ℕ)
    (hm : ∀ i t, localRecords (input i).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove (S.high d) ((route i).origin v) = t) ≤ M) (j : Fin run.expansion.terms) (t) :
    1+localRecords (run.expansion.pack j).layout ex (run.expansionBankRecords fields j).prior
      (run.expansionBankRecords fields j).payload (fun v => reduceMove (d+1) ((run.expansion.routes j).origin v) = t) ≤
        S.bankRecordFactor*(1+M) := by
  let q := run.enum j
  let result := run.partialBankFields fields S.rounds le_rfl id q
  have replay := run.partialBankFields_bound fields ex M hm S.rounds le_rfl id q
  have rounded := flat_output_record_bound (Mch.F.terminal run.flat q) (run.out q) result ex (by positivity) replay t
  exact rounded.trans_eq (by unfold SiteSchedule.bankRecordFactor epochRecordFactor; ring)

end SiteExecution
end PackedHistoryCircuit.Normalized

namespace Packing.PhysicalEpochs.ExecutedRecords

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive
open scoped Classical
open private cap_reindex from OAI.Computability.BorderVNP.PackedSiteRecords
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
variable (U : Factory.Dense.Programs S) {start T : ℕ} (deep : S.floor+1+S.drop*T ≤ start)

/-- Feed each normalized epoch's actual cumulative fields into the next epoch of the outer tree. -/
noncomputable def denseBankRecordStep (t : ℕ)
    (child : Fin (S.fanIn^S.rounds) → (Factory.ofDenseSchedule U).State bits start t)
    (data : ∀ i, RecordData (child i).pack.layout) :
    (Factory.ofDenseSchedule U).RecordStep child data ((Factory.ofDenseSchedule U).epoch deep t child) S.bankRecordFactor := by
  let F := Factory.ofDenseSchedule U
  by_cases ht : t < T
  · let input := fun i => (child i).pack
    let route := fun i => reindexRoutes (F.levels deep ht).2.2.symm (child i).route
    let actual := U.run _ (F.levels deep ht).1 _ _ input route
    let H := actual.expansion
    let Z : ProfileSum (F.State bits start (t+1)) :=
      ⟨Fin H.terms,inferInstance,fun j => ⟨H.pack j,reindexRoutes (F.levels deep ht).2.1 (H.routes j)⟩⟩
    rw [show F.epoch deep t child = Z from dite_eq_left ht]
    refine ⟨actual.expansionBankRecords data,?_⟩
    intro ex B hc j
    have hchild (i) := (cap_reindex (child i).route (F.levels deep ht).2.2.symm (data i) ex B).mpr (hc i)
    have hfan : 0 < F.fan := pow_pos S.positiveFanIn _
    have hpos := hchild ⟨0,hfan⟩ 1
    have hB : 1+(B-1) = B := by omega
    let tested (f : Fintype (Port F.fan P (t+1))) := @SiteCap D K _ _ f _ _ _ _
      (Z.term j).pack (Z.term j).route (actual.expansionBankRecords data j) ex (S.bankRecordFactor*B)
    apply (congrArg tested (Subsingleton.elim (portFintype (P := P) (k := F.fan) (b := t+1))
      (instFintypeProd (Fin F.fan) (Port F.fan P t)))).mpr
    apply (cap_reindex (H.routes j) (F.levels deep ht).2.1 _ ex _).mpr
    intro tile
    have bound := actual.expansionBankRecords_bound data ex (B-1) (fun i x => by
      apply Nat.le_sub_of_add_le
      rw [Nat.add_comm]
      exact hchild i x) j tile
    rwa [hB] at bound
  · let Z : ProfileSum (F.State bits start (t+1)) := ⟨Empty,inferInstance,Empty.elim⟩
    rw [show F.epoch deep t child = Z from dite_eq_right ht]
    exact ⟨fun j => Empty.elim j,fun _ _ _ j => Empty.elim j⟩

/-- The schedule's cumulative bank factor bounds every attained normalized outer history
at every routed site tile after any number of complete epochs. -/
theorem denseBankHistory_bound (bottom : (Factory.ofDenseSchedule U).State bits start 0)
    (base : RecordData bottom.pack.layout) (ex : Bool) (B : ℕ) (hbase : SiteCap bottom.route base ex B)
    (t : ℕ) (j : ((Factory.ofDenseSchedule U).histories deep bottom t).Index) :
    SiteCap (((Factory.ofDenseSchedule U).histories deep bottom t).term j).route
      ((Factory.ofDenseSchedule U).historyRecords deep (denseBankRecordStep U deep) bottom base t j) ex (S.bankRecordFactor^t*B) :=
  (Factory.ofDenseSchedule U).historyRecords_bound deep (denseBankRecordStep U deep) bottom base ex B hbase t j

end Packing.PhysicalEpochs.ExecutedRecords

end BorderVNP
end Computability
end OAI
