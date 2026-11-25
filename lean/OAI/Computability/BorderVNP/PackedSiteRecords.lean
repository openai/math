import OAI.Computability.BorderVNP.PackedSiteEpochs
import OAI.Computability.BorderVNP.ShortenEpochRoundExecutionRecords

/-! # Retained records of each selected outer profile history

The metadata on every original site survives input subdivision. Each actual
inner replacement and final site rounding transports those records and
introduces its own new public descriptors and private payload. The same
physical output and metadata work for both counting modes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PhysicalEpochs

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive
open scoped Classical
attribute [local instance] portFintype

variable {D : ℕ} {K : Type*} [Field K]

/-- A bound on one plus the exact local record count at every site of a
physically routed pack. -/
def SiteCap {P I : Type} [Fintype P] [Fintype I] {bits : P → ℕ} {d : ℕ} {L : ℝ}
    {p : Pack D P bits K} (r : SiteRoutes p I d L) (fields : RecordData p.layout)
    (ex : Bool) (B : ℕ) := ∀ tile, 1 + localRecords p.layout ex fields.prior fields.payload
      (fun v => reduceMove d (r.origin v) = tile) ≤ B

omit [Field K] in
private theorem cap_reindex {P I : Type} [Fintype P] [Fintype I] {bits : P → ℕ} {a d : ℕ} {L : ℝ}
    {p : Pack D P bits K} (r : SiteRoutes p I a L) (eq : a = d) (fields : RecordData p.layout)
    (ex : Bool) (B : ℕ) :
    SiteCap (reindexRoutes eq r) fields ex B ↔ SiteCap r fields ex B := by cases eq; rfl

namespace Factory

variable (F : Factory D K) {P : Type} [Fintype P] {bits : P → ℕ} {start T : ℕ}

/-- The actual additional metadata on the physical outputs of this particular
tuple, carrying both local bounds for exactly those chosen fields. -/
structure RecordStep {t : ℕ} (child : Fin F.fan → F.State bits start t)
    (data : ∀ i, RecordData (child i).pack.layout)
    (outputs : ProfileSum (F.State bits start (t+1))) (C : ℕ) where
  /-- Retained fields on every physical output box. -/
  fields : ∀ j, RecordData (outputs.term j).pack.layout
  /-- The single physical record multiplier applies at all tiles in both modes. -/
  bound : ∀ (ex : Bool) (B : ℕ), (∀ i, SiteCap (child i).route (data i) ex B) →
    ∀ j, SiteCap (outputs.term j).route (fields j) ex (C*B)

variable (deep : F.floor + 1 + F.drop*T ≤ start) {C : ℕ}
variable (extend : ∀ t (child : Fin F.fan → F.State bits start t) (data : ∀ i, RecordData (child i).pack.layout),
  F.RecordStep child data (F.epoch deep t child) C)
variable (bottom : F.State bits start 0) (base : RecordData bottom.pack.layout)

/-- Traverse the selected child tuple and use its own parent's physical
record transfer. The resulting fields refer to precisely that final pack. -/
noncomputable def historyRecords : (t : ℕ) → (j : (F.histories deep bottom t).Index) →
    RecordData ((F.histories deep bottom t).term j).pack.layout
  | 0, _ => base
  | t+1, j => (extend t (fun i => (F.histories deep bottom t).term (j.1 i))
      (fun i => historyRecords t (j.1 i))).fields j.2

/-- A true selected history transports the initial tile cap through all
physical epochs with the same fixed per-epoch factor. -/
theorem historyRecords_bound (ex : Bool) (B : ℕ) (hbase : SiteCap bottom.route base ex B)
    (t : ℕ) (j : (F.histories deep bottom t).Index) :
    SiteCap ((F.histories deep bottom t).term j).route (F.historyRecords deep extend bottom base t j) ex (C^t*B) := by
  induction t with
  | zero => simpa [historyRecords,histories,packHistory] using hbase
  | succ t ih =>
    let child := fun i => (F.histories deep bottom t).term (j.1 i)
    let data := fun i => F.historyRecords deep extend bottom base t (j.1 i)
    have h := (extend t child data).bound ex (C^t*B) (fun i => ih (j.1 i)) j.2
    rw [pow_succ',Nat.mul_assoc]
    unfold historyRecords
    exact h

end Factory

namespace ExecutedRecords

variable [NeZero D] {m : ℕ} {e : PaidIdentity K D m} (S : SiteSchedule e)
variable (machine : ∀ d ≥ S.floor, ∀ (P : Type) [Fintype P] (bits : P → ℕ), S.Machine d P bits)
variable (run : ∀ d (hd : d ≥ S.floor) (P : Type) [Fintype P] (bits : P → ℕ)
  (input : Fin (S.fanIn^S.rounds) → Pack D P bits K)
  (route : ∀ i, SiteRoutes (input i) (Cube D) (S.inputLevel d) S.budget), S.Execution (machine d hd P bits) input route)
variable {P : Type} [Fintype P] {bits : P → ℕ} {start T : ℕ}
variable (deep : S.floor + 1 + S.drop*T ≤ start)

set_option maxHeartbeats 1200000 in
/-- Instantiate every outer-node metadata transfer with the subdivision,
retained sewing fields, final rounding and port flattening of its genuine
site execution. -/
noncomputable def recordStep (t : ℕ) (child : Fin (S.fanIn^S.rounds) → (Factory.ofSchedule S machine run).State bits start t)
    (data : ∀ i, RecordData (child i).pack.layout) :
    (Factory.ofSchedule S machine run).RecordStep child data
      ((Factory.ofSchedule S machine run).epoch deep t child) S.recordFactor := by
  let F := Factory.ofSchedule S machine run
  change F.RecordStep child data (F.epoch deep t child) S.recordFactor
  by_cases ht : t < T
  · let low := F.depth start (t+1) - 1
    let hd := (F.levels deep ht).1
    let input := fun i => (child i).pack
    let route := fun i => reindexRoutes (F.levels deep ht).2.2.symm (child i).route
    let actual := run low hd _ _ input route
    let H := actual.expansion
    let Z : ProfileSum (F.State bits start (t+1)) :=
      ⟨Fin H.terms,inferInstance,fun j => ⟨H.pack j,reindexRoutes (F.levels deep ht).2.1 (H.routes j)⟩⟩
    rw [show F.epoch deep t child = Z from dite_eq_left ht]
    refine ⟨actual.expansionRecords data,?_⟩
    intro ex B hc j
    have hc' (i) := (cap_reindex (child i).route (F.levels deep ht).2.2.symm (data i) ex B).mpr (hc i)
    have hfan : 0 < F.fan := pow_pos S.positiveFanIn _
    have hpos := hc' ⟨0,hfan⟩ 1
    have hB : 1+(B-1) = B := by omega
    let tested (f : Fintype (Port F.fan P (t+1))) := @SiteCap D K _ _ f _ _ _ _
      (Z.term j).pack (Z.term j).route (actual.expansionRecords data j) ex (S.recordFactor*B)
    apply (congrArg tested (Subsingleton.elim (portFintype (P := P) (k := F.fan) (b := t+1))
      (instFintypeProd (Fin F.fan) (Port F.fan P t)))).mpr
    apply (cap_reindex (H.routes j) (F.levels deep ht).2.1 _ ex _).mpr
    intro tile
    have bound := S.recordCertificate actual data ex (B-1) (fun i x => by
      apply Nat.le_sub_of_add_le
      rw [Nat.add_comm]
      exact hc' i x) j tile
    rwa [hB] at bound
  · let Z : ProfileSum (F.State bits start (t+1)) := ⟨Empty,inferInstance,Empty.elim⟩
    rw [show F.epoch deep t child = Z from dite_eq_right ht]
    exact ⟨fun j => Empty.elim j,fun _ _ _ j => Empty.elim j⟩

end ExecutedRecords
end Packing.PhysicalEpochs

end BorderVNP
end Computability
end OAI
