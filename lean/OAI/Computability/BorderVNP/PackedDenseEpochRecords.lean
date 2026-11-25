import OAI.Computability.BorderVNP.PackedSiteRecords
import OAI.Computability.BorderVNP.PackedDenseFactory
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseExecutionRecords

/-! # Retained metadata of the public sorted outer history

Every selected physical tuple uses the specific normalized machine, before
and after cable orders, and terminal motion saved by the factory. Its actual
record fields satisfy the local resource bound across all outer epochs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PhysicalEpochs.ExecutedRecords

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive
open scoped Classical
open private cap_reindex from OAI.Computability.BorderVNP.PackedSiteRecords
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
variable (U : Factory.Dense.Programs S) {start T : ℕ}
variable (deep : S.floor+1+S.drop*T ≤ start)

set_option maxHeartbeats 1000000 in
/-- Retained input metadata, new histogram boxes, and final motion are those
of this exact site execution with its two public row orderings. -/
noncomputable def denseRecordStep (t : ℕ)
    (child : Fin (S.fanIn^S.rounds) → (Factory.ofDenseSchedule U).State bits start t)
    (data : ∀ i, RecordData (child i).pack.layout) :
    (Factory.ofDenseSchedule U).RecordStep child data ((Factory.ofDenseSchedule U).epoch deep t child) S.recordFactor := by
  let F := Factory.ofDenseSchedule U
  change F.RecordStep child data (F.epoch deep t child) S.recordFactor
  by_cases ht : t < T
  · let input := fun i => (child i).pack
    let route := fun i => reindexRoutes (F.levels deep ht).2.2.symm (child i).route
    let actual := U.run _ (F.levels deep ht).1 _ _ input route
    let H := actual.expansion
    let Z : ProfileSum (F.State bits start (t+1)) :=
      ⟨Fin H.terms,inferInstance,fun j => ⟨H.pack j,reindexRoutes (F.levels deep ht).2.1 (H.routes j)⟩⟩
    rw [show F.epoch deep t child = Z from dite_eq_left ht]
    refine ⟨actual.expansionRecords data,?_⟩
    intro ex B hc j
    have hchild (i) := (cap_reindex (child i).route (F.levels deep ht).2.2.symm (data i) ex B).mpr (hc i)
    have hfan : 0 < F.fan := pow_pos S.positiveFanIn _
    have hpos := hchild ⟨0,hfan⟩ 1
    have hB : 1+(B-1) = B := by omega
    let tested (f : Fintype (Port F.fan P (t+1))) := @SiteCap D K _ _ f _ _ _ _
      (Z.term j).pack (Z.term j).route (actual.expansionRecords data j) ex (S.recordFactor*B)
    apply (congrArg tested (Subsingleton.elim (portFintype (P := P) (k := F.fan) (b := t+1))
      (instFintypeProd (Fin F.fan) (Port F.fan P t)))).mpr
    apply (cap_reindex (H.routes j) (F.levels deep ht).2.1 _ ex _).mpr
    intro tile
    have bound := actual.expansionRecords_bound data ex (B-1) (fun i x => by
      apply Nat.le_sub_of_add_le
      rw [Nat.add_comm]
      exact hchild i x) j tile
    rwa [hB] at bound
  · let Z : ProfileSum (F.State bits start (t+1)) := ⟨Empty,inferInstance,Empty.elim⟩
    rw [show F.epoch deep t child = Z from dite_eq_right ht]
    exact ⟨fun j => Empty.elim j,fun _ _ _ j => Empty.elim j⟩

/-- Both modes on the actual original metadata retained by each final
sorted history are bounded by the fixed normalized record factor per epoch. -/
theorem denseHistoryRecords_bound (bottom : (Factory.ofDenseSchedule U).State bits start 0)
    (base : RecordData bottom.pack.layout) (ex : Bool) (B : ℕ) (hbase : SiteCap bottom.route base ex B)
    (t : ℕ) (j : ((Factory.ofDenseSchedule U).histories deep bottom t).Index) :
    SiteCap (((Factory.ofDenseSchedule U).histories deep bottom t).term j).route
      ((Factory.ofDenseSchedule U).historyRecords deep (denseRecordStep U deep) bottom base t j) ex (S.recordFactor^t*B) :=
  (Factory.ofDenseSchedule U).historyRecords_bound deep (denseRecordStep U deep) bottom base ex B hbase t j

end Packing.PhysicalEpochs.ExecutedRecords

end BorderVNP
end Computability
end OAI
