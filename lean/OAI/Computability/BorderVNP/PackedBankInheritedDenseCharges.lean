import OAI.Computability.BorderVNP.PackedBankRoundSites
import OAI.Computability.BorderVNP.PackedInheritedDenseOrder
import OAI.Computability.BorderVNP.PackedInheritedParallelOrder
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseReplay

/-! # Cumulative bank charges on the stable public cable order

The normalized stage sorts the disjoint input cables before allocating bands.
Its record test is the sum of the constituent tests, and each input site retains
its own child's incident widths. The chosen histogram pays for the cumulative
bank fields and the actual installed programs with the dense geometric factor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedBank

open Crossing Inherited
open scoped Classical

variable {D E : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits) (slot : N.Edge ↪ Fin E) (v : N.Site)

/-- Stable compaction preserves the sum of the distinct incident cable widths at a site. -/
theorem dense_incidentWidth : incidentWidth (Names.denseLayout N slot) v = incidentWidth N v :=
  (Fintype.sum_equiv (denseIncident N slot v) _ _ fun c => (dense_width N slot c.val).symm).symm

/-- External port widths and their attachment sites survive stable compaction. -/
theorem dense_portWidth [Fintype P] : portWidth (Names.denseLayout N slot) v = portWidth N v := rfl

end Packing.InheritedBank

namespace PackedHistoryCircuit.Normalized.Stage

open Crossing Cover Epoch Epoch.Round Packing Packing.Inherited Packing.InheritedBank Shortening
open scoped Classical

variable {D m k d d' : ℕ} [NeZero D] {K : Type*} [Field K] {I B P : Type}
    [Fintype I] [Fintype B] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    (s : Stage m B d' child) (j : Fin k) (v : (child j).pack.layout.Site)

omit [Field K] in
/-- The sorted input site's incident cables have exactly the widths of its child's cables. -/
theorem input_incidentWidth : incidentWidth s.input.layout ⟨j,v⟩ = incidentWidth (child j).pack.layout v := by
  refine (dense_incidentWidth (raw child).layout s.slot ⟨j,v⟩).trans ?_
  exact (Fintype.sum_equiv (Inherited.Parallel.incident (fun i => (child i).pack.layout) j v) _ _ fun _ => rfl).symm

variable [Fintype P]

omit [Field K] in
/-- The sorted input site's external ports belong to its child with all original widths. -/
theorem input_portWidth : portWidth s.input.layout ⟨j,v⟩ = portWidth (child j).pack.layout v := by
  refine (dense_portWidth (raw child).layout s.slot ⟨j,v⟩).trans ?_
  exact (Fintype.sum_equiv (Inherited.Parallel.attached (fun i => (child i).pack.layout) j v) _ _ fun _ => rfl).symm

omit [Field K] in
/-- A stored child's program has the same incoming capacity on the normalized input. -/
theorem input_incoming : incoming s.input.layout ⟨j,v⟩ = incoming (child j).pack.layout v :=
  (dense_incoming (raw child).layout s.slot ⟨j,v⟩).trans
    (Inherited.Parallel.incoming_eq (fun i => (child i).pack.layout) j v)

variable (data : ∀ i, RecordData (child i).pack.layout)

omit [Field K] in
/-- Any tested region on the normalized input has exactly the sum of the constituent child loads. -/
theorem input_localRecords (ex : Bool) (test : s.input.layout.Site → Prop) :
    localRecords s.input.layout ex (fun v => (data v.1).prior v.2) (fun v => (data v.1).payload v.2) test =
      ∑ i, localRecords (child i).pack.layout ex (data i).prior (data i).payload (fun v => test ⟨i,v⟩) :=
  (Names.localRecords_denseLayout (raw child).layout s.slot ex _ _ test).trans
    (parallel_localRecords (fun i => (child i).pack) ex (fun i => (data i).prior) (fun i => (data i).payload)
      (fun i v => test ⟨i,v⟩))

omit [Field K] in
/-- The largest constituent load bounds the complete input test with the actual fan-in. -/
theorem input_localRecords_le_max (ex : Bool) (test : s.input.layout.Site → Prop) :
    localRecords s.input.layout ex (fun v => (data v.1).prior v.2) (fun v => (data v.1).payload v.2) test ≤
      k * Finset.univ.sup (fun i => localRecords (child i).pack.layout ex (data i).prior (data i).payload
        (fun v => test ⟨i,v⟩)) := by
  rw [s.input_localRecords data ex test]
  let count := fun i => localRecords (child i).pack.layout ex (data i).prior (data i).payload (fun v => test ⟨i,v⟩)
  exact (Finset.sum_le_sum (fun i _ => Finset.le_sup (s := Finset.univ) (f := count) (Finset.mem_univ i))).trans_eq
    (by simp [count])

variable (e : PaidIdentity K D m) (q : s.Index e)

/-- The cumulative site fields on the actual stable-order output of this selected histogram. -/
noncomputable def bankRecordData (data : ∀ i, RecordData (child i).pack.layout) : RecordData (s.result e q).pack.layout :=
  ⟨nextPrior e s.input s.label s.perm s.orient (0,false) q (fun v => (data v.1).prior v.2),
   nextPayload e s.input s.label s.perm s.orient (0,false) q (fun v => (data v.1).payload v.2)⟩

private theorem within_of_result_load (result : RecordData (s.result e q).pack.layout) {C : ℕ}
    (cert : s.RecordFactor e C) (ex : Bool) (T : ℕ) (hT : 0 < T)
    (old : ∀ i, RecordsWithin (child i) (data i) ex T)
    (load : ∀ t, localRecords (s.result e q).pack.layout ex result.prior result.payload
      (fun v => productTileName d' ((s.result e q).site v) = t) ≤
      loadMultiplier e * s.resultLocalRecords e q ex (fun i => (data i).prior) (fun i => (data i).payload) t) :
    RecordsWithin (s.result e q) result ex (loadMultiplier e*C*k*T) := by
  let prior := fun i => (data i).prior
  let payload := fun i => (data i).payload
  have cap := cert q ex prior payload (T-1) (fun i t => by
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm]
    exact old i t)
  rw [show 1+(T-1) = T by omega] at cap
  have unit : 1 ≤ loadMultiplier e := by unfold loadMultiplier; omega
  intro t
  calc
    _ ≤ loadMultiplier e + loadMultiplier e * s.resultLocalRecords e q ex prior payload t := Nat.add_le_add unit (load t)
    _ = loadMultiplier e * (1+s.resultLocalRecords e q ex prior payload t) := by rw [Nat.mul_add,Nat.mul_one]
    _ ≤ loadMultiplier e * (C*k*T) := Nat.mul_le_mul_left _ (cap t)
    _ = _ := by simp only [Nat.mul_assoc]

/-- The prepared dense geometric certificate bounds every tile of the cumulative result. -/
theorem bankRecordData_within (data : ∀ i, RecordData (child i).pack.layout) {C : ℕ}
    (cert : s.RecordFactor e C) (ex : Bool) (T : ℕ) (hT : 0 < T) (old : ∀ i, RecordsWithin (child i) (data i) ex T) :
    RecordsWithin (s.result e q) (s.bankRecordData e q data) ex (loadMultiplier e*C*k*T) := by
  apply within_of_result_load s data e q _ cert ex T hT old
  intro t
  exact output_load_le e s.input s.label s.perm s.orient (0,false) q ex
    (fun v => (data v.1).prior v.2) (fun v => (data v.1).payload v.2) _

variable {ns ne np : ℕ} (siteID : (s.result e q).pack.layout.Site ↪ Fin ns)
    (edgeID : (s.result e q).pack.layout.Edge ↪ Fin ne) (portID : Fin k × P ↪ Fin np)
    (binName : ((I → Deck (d'+1)) × B) → ℕ) (position : e.Entry → ℕ)
    (programs : ∀ i, (child i).pack.layout.Site → Site) (cuts : s.input.layout.Site → List Slice)

/-- The concrete programs installed in public cut order fit the geometric step's per-tile
cap when their child programs fit their own incoming sizes and resource fields. -/
theorem roundSites_within {C : ℕ} (cert : s.RecordFactor e C) (ex : Bool) (T : ℕ) (hT : 0 < T)
    (old : ∀ i, RecordsWithin (child i) (data i) ex T)
    (incomingChild : ∀ i v, (programs i v).incoming = incoming (child i).pack.layout v)
    (fields : ∀ i v, (programs i v).staticNodes ≤ (data i).prior v ∧ (programs i v).expandedLoad ≤ (data i).payload v)
    (sorted : ∀ v, (cuts v).Perm (layerCuts e s.input s.label s.perm binName s.orient (0,false) q v
      (CutCircuit.denseRows (raw child).layout s.slot) edgeID portID)) :
    let installed := roundSites e s.input s.label s.perm s.orient (0,false) q binName position siteID edgeID portID
      (fun v => programs v.1 v.2) cuts
    RecordsWithin (s.result e q) ⟨fun v => (installed v).staticNodes,fun v => (installed v).expandedLoad⟩ ex
      (loadMultiplier e*C*k*T) := by
  intro installed
  apply within_of_result_load s data e q _ cert ex T hT old
  intro t
  exact roundSites_load_le e s.input s.label s.perm s.orient (0,false) q binName position siteID edgeID portID
    (fun v => programs v.1 v.2) cuts ex (fun v => (data v.1).prior v.2) (fun v => (data v.1).payload v.2)
    (fun v => (incomingChild v.1 v.2).trans (s.input_incoming v.1 v.2).symm) (fun v => fields v.1 v.2)
    (cuts_length_of_perm e s.input s.label s.perm s.orient (0,false) q binName edgeID portID cuts _ sorted) _

end PackedHistoryCircuit.Normalized.Stage

end BorderVNP
end Computability
end OAI
