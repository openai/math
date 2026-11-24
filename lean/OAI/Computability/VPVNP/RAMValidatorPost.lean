import OAI.Computability.VPVNP.RAMValidatorRecords
import OAI.Computability.VPVNP.RAMValidatorSuccessor
import OAI.Computability.VPVNP.RAMValidatorBoundary
import OAI.Computability.VPVNP.RAMSortScanMessages

/-!
# Deterministic memory pass of the site validator

After a successful bucket simulation, the site fills its sorting buffer from
its header and the returned reports. It runs the bitonic layers on the incident
bit vector and checks every read and the outgoing last physical slot.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMLayout RAMSort RAMMemory

variable {d e w : ℕ}

/-- This computation accesses just the local header, reports, and incident
array. Its result includes the work on malformed sorting fields. -/
def checkSiteMemory (hw : 2 ≤ w) (v : Fin (2^d)) (header : Word w) (raw : ℕ → Bool)
    (edges : SiteSuccessors w) (rs : List (Report w)) : Bool × ℕ :=
  let records := recordBuffer e v.val header edges.input.cost rs
  let sorted := scanSort hw raw v records.1
  let boundary := RAMBoundary.scan edges.received
    (if v.val+1 < 2^d then some edges.sent else none) (fun i => (sorted.block i).record)
  (sorted.ok && boundary.1, records.2 + sorted.steps + boundary.2 + 8)

theorem checkSiteMemory_iff (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : SendArrays d (2^e) w)
    (v : Fin (2^d)) (header : ℕ → Word w) (initial : Word w) (edges : SiteSuccessors w)
    (he : edges.Spec hw hc initial v a) (rs : List (Report w)) :
    (checkSiteMemory (e := e) hw v (header v) (sortIncident a v) edges rs).1 = true ↔
      SortCanonical hw hc a v ∧ MemoryAt (unpackMessages (parseMessages hw hc a)).memory v
        (localRecords header e v.val edges.input.cost rs) := by
  let records := localRecords header e v.val edges.input.cost rs
  let m := (unpackMessages (parseMessages hw hc a)).memory
  let sorted := scanStages hw (sortIncident a v) v (phases ((2+e)+d) ((2+e)+d) le_rfl) records
  simp only [checkSiteMemory, recordBuffer_data, Bool.and_eq_true, scanSort_ok, scanSort_block, he.received_eq, he.sent_eq]
  change (sorted.ok = true ∧ _) ↔ SortCanonical hw hc a v ∧ MemoryAt m v records
  rw [sortScan_messages hw hc a v records, RAMBoundary.scan_spec (Nat.two_pow_pos _)]
  constructor
  · rintro ⟨⟨hcan, hsort⟩, hbound⟩
    rw [sortScan_output hw hc a v records hcan] at hbound
    exact ⟨hcan, hsort, hbound⟩
  · rintro ⟨hcan, hsort, hbound⟩
    rw [sortScan_output hw hc a v records hcan]
    exact ⟨⟨hcan, hsort⟩, hbound⟩

/-- The memory pass runs only after the bucket simulation succeeded. Its
bound needs no validity hypothesis on the sorting or successor bits. -/
theorem checkSiteMemory_work {C : Type*} {P : Program w C} {fuel : ℕ} (hw : 2 ≤ w)
    (v : Fin (2^d)) (header : Word w) (raw : ℕ → Bool) (edges : SiteSuccessors w)
    (rs : List (Report w)) (hs : SiteRun P fuel (2^d) (2^e) v.val edges.input rs) :
    (checkSiteMemory (e := e) hw v header raw edges rs).2 ≤
      90 + (2 * 2^e) * (12 * fuel + 9) + 64 * (4 * 2^e) +
        (((2+e)+d)+1).choose 2 * (4*2^e * (1024*(w+1)) + 9) := by
  let records := recordBuffer e v.val header edges.input.cost rs
  let sorted := scanSort hw raw v records.1
  have hr := recordBuffer_work header hs
  have hsort := scanSort_cost hw raw v records.1
  have hb := RAMBoundary.scan_cost edges.received
    (if v.val+1 < 2^d then some edges.sent else none) (fun i => (sorted.block i).record)
  change records.2 ≤ _ at hr
  change sorted.steps ≤ _ at hsort
  rw [record_width] at hsort
  conv_rhs at hb => rw [record_width]
  change records.2 + sorted.steps + (RAMBoundary.scan edges.received
    (if v.val+1 < 2^d then some edges.sent else none) (fun i => (sorted.block i).record)).2 + 8 ≤ _
  omega

end BurstRAM

end VPVNP
end Computability
end OAI
