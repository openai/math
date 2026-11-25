import OAI.Computability.BorderVNP.PackedEnrichedEpochRecords
import OAI.Computability.BorderVNP.PackedHistoryNormalizedMachine
import OAI.Computability.BorderVNP.PackedSiteRecords

/-! # Records in the selected history of the named processor machine

The metadata of the children follows their actual routed state, allocated
rows and public words. The parent transports it through exactly the chosen
normalized program on that tuple, using one schedule-dependent multiplier.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Adaptive PublicCapacity PhysicalEpochs
open scoped Classical BorderVNP.Epoch.Cube
open private cap_reindex from OAI.Computability.BorderVNP.PackedSiteRecords
attribute [local instance] portFintype

universe u

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
variable {start T : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape} {W : ℕ → Type}
variable [∀ t, Fintype (W t)] {deep : S.floor+1+S.drop*T ≤ start}
variable {good : ∀ t, State S start P bits shape W t → Prop}

/-- Metadata returned at each true histogram and its two physical tile cap
estimates. The record factor and the selected geometry refer to the same run. -/
structure ReturnedFields {t : ℕ} (c : Fin (fan S) → Admissible good t)
    (fields : ∀ i, RecordData (c i).val.pack.layout) (Z : ProfileSum (Admissible good (t+1))) where
  /-- Inherited data and newly installed profile records. -/
  field : ∀ j, RecordData (Z.term j).val.pack.layout
  /-- Both record modes use the same field maps on these branches. -/
  bound : ∀ ex B, (∀ i, SiteCap (c i).val.route (fields i) ex B) →
    ∀ j, SiteCap (Z.term j).val.route (field j) ex (S.recordFactor*B)

namespace Epoch

variable {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (c : Fin (fan S) → Admissible good t)

set_option maxHeartbeats 1200000 in
/-- Actual fields of every output of this one named epoch. The source may
distinguish copies with the same unlabelled tensor and different sidecars. -/
noncomputable def returnedFields (fields : ∀ i, RecordData (c i).val.pack.layout) :
    ReturnedFields c fields (E.choice c) := by
  let run := E.run c
  refine ⟨fun q => run.recordFields fields E.saveNames q,?_⟩
  intro ex B hc j
  have hchild (i) := (cap_reindex (c i).val.route (levels S deep ht).2.2.symm (fields i) ex B).mpr (hc i)
  have hfan : 0 < fan S := pow_pos S.positiveFanIn _
  have hpos := hchild ⟨0,hfan⟩ 1
  have hB : 1+(B-1) = B := by omega
  let state := (E.term c j).val
  let tested (f : Fintype (Port (fan S) P (t+1))) := @SiteCap D K _ _ f _ _ _ _
    state.pack state.route (run.recordFields fields E.saveNames j) ex (S.recordFactor*B)
  apply (congrArg tested (Subsingleton.elim (portFintype (P := P) (k := fan S) (b := t+1))
    (instFintypeProd (Fin (fan S)) (Port (fan S) P t)))).mpr
  apply (cap_reindex (run.output.out j).routes.flatten (levels S deep ht).2.1 _ ex _).mpr
  intro tile
  have bound := run.recordCertificate fields E.saveNames E.records ex (B-1) (fun i x => by
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm]
    exact hchild i x) j tile
  rwa [hB] at bound

end Epoch

namespace Machine

variable {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
variable (M : Machine.{_,u} deep good V w)

/-- Fields and cap for the actual branch index used by the outer profile tree. -/
noncomputable def nodeRecords (t : ℕ) (c : Fin (fan S) → Admissible good t)
    (fields : ∀ i, RecordData (c i).val.pack.layout) :
    ReturnedFields c fields (M.epoch t c) := by
  by_cases ht : t<T
  · rw [show M.epoch t c = (M t ht).choice c from dite_eq_left ht]
    exact (M t ht).returnedFields c fields
  · let empty : ProfileSum (Admissible good (t+1)) := ⟨Empty,inferInstance,Empty.elim⟩
    rw [show M.epoch t c = empty from dite_eq_right ht]
    exact ⟨fun j => Empty.elim j,fun _ _ _ j => Empty.elim j⟩

variable (bottom : Admissible good 0) (base : RecordData bottom.val.pack.layout)

/-- Recover the true accumulated box records from one selected complete
outer history, preserving the geometry and words of each chosen child. -/
noncomputable def historyFields : (t : ℕ) → (j : (packHistory bottom M.epoch t).Index) →
    RecordData ((packHistory bottom M.epoch t).term j).val.pack.layout
  | 0, _ => base
  | t+1, j => (M.nodeRecords t (fun i => (packHistory bottom M.epoch t).term (j.1 i))
      (fun i => historyFields t (j.1 i))).field j.2

/-- Both record modes at all selected terminal sites obey the iterated
factor times the initial tile cap. -/
theorem historyFields_bound (ex : Bool) (B : ℕ) (hbase : SiteCap bottom.val.route base ex B)
    (t : ℕ) (q : (packHistory bottom M.epoch t).Index) :
    SiteCap ((packHistory bottom M.epoch t).term q).val.route (M.historyFields bottom base t q) ex (S.recordFactor^t*B) := by
  induction t with
  | zero =>
    change SiteCap bottom.val.route base ex (S.recordFactor^0*B)
    simpa only [pow_zero,one_mul] using hbase
  | succ t ih =>
    rw [pow_succ',Nat.mul_assoc]
    unfold historyFields
    exact (M.nodeRecords t _ _).bound ex (S.recordFactor^t*B) (fun i => ih (q.1 i)) q.2

end Machine
end PackedHistoryCircuit.Normalized.EnrichedOuter

end BorderVNP
end Computability
end OAI
