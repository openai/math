import OAI.Computability.VPVNP.RAMBoundary
import OAI.Computability.VPVNP.RAMRecordIndex
import OAI.Computability.VPVNP.RAMSortedRecords
import OAI.Computability.VPVNP.RAMSortFieldEquiv

/-!
# The memory checks in a single site's transcript

Starting with its own padded records, a site verifies its outgoing messages,
replays the sorting layers using the prescribed partners, and checks reads
against preceding slots. Together these independent checks enforce the true
memory semantics and uniquely determine all sorting and last-record fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMMemory RAMSort

/-- Blocks of ordered record slots sent by each site at each cross-site sorting layer. -/
abbrev SortSends (h d w : ℕ) :=
  RAMLayout.Layer d → Fin (2 ^ d) → Wires h (OrderedSlot (Word w))

/-- All outgoing sorting blocks and the last sorted records passed along successor links for
the memory check. -/
@[ext] structure MemoryMessages (h d w : ℕ) where
  /-- Claimed outgoing record block for every site at every cross-site sorting layer. -/
  sortSends : SortSends h d w
  /-- Claimed last record sent to each succeeding site for checking the boundary of its sorted
  block. -/
  lastRecords : RAMBoundary.Sends (2 ^ d) (Word w)

variable {h d w : ℕ}

private abbrev schedule (h d : ℕ) := phases (h + d) (h + d) le_rfl

/-- The final local block is computed from the local records and the incident
sort sends, with the receive for each cross-layer taken from its XOR partner. -/
def outputAt (m : MemoryMessages h d w) (v : Fin (2^d)) (input : Wires h (OrderedSlot (Word w))) :
    Wires h (Option (Record (Word w))) :=
  fun i => (replay v (schedule h d) (physicalFieldsEquiv.{0,0} h d _ m.sortSends) input i).record

/-- The site passes its sorting-layer message checks and verifies its output reads using the
predecessor record at its block boundary. -/
def MemoryAt (m : MemoryMessages h d w) (v : Fin (2^d)) (input : Wires h (OrderedSlot (Word w))) :
    Prop :=
  checks v (schedule h d) (physicalFieldsEquiv.{0,0} h d _ m.sortSends) input ∧
    RAMBoundary.checkAt (Nat.two_pow_pos h) m.lastRecords v (outputAt m v input)

/-- The site's block after running the full sorting network, with each ordered slot projected
to its optional memory record. -/
def sortedBlock (h d : ℕ) (x : ℕ → OrderedSlot (Word w)) (v : Fin (2^d)) :
    Wires h (Option (Record (Word w))) :=
  fun i => (block h v.val (runPhases (h + d) x) i).record

/-- The genuine sorting messages and predecessor records, computed in their
order of use. -/
def actualMemoryMessages (h d : ℕ) (x : ℕ → OrderedSlot (Word w)) : MemoryMessages h d w where
  sortSends := (physicalFieldsEquiv.{0,0} h d _).symm (actual (schedule h d) x)
  lastRecords := RAMBoundary.actual (Nat.two_pow_pos h) (sortedBlock h d x)

/-- Local checks force both families of messages. The only remaining test is
the immediate-predecessor rule in the sorted array. -/
theorem memoryAt_iff (m : MemoryMessages h d w) (x : ℕ → OrderedSlot (Word w)) :
    (∀ v, MemoryAt m v (block h v.val x)) ↔
      m = actualMemoryMessages h d x ∧
      PaddedCheck none (RAMBoundary.flat (sortedBlock h d x)) := by
  constructor
  · intro hm
    have hc := fun v => (hm v).1
    have hout (v) : outputAt m v (block h v.val x) = sortedBlock h d x v := by
      funext i
      exact congrArg (fun f : Wires h (OrderedSlot (Word w)) => (f i).record)
        (replay_phases _ x hc v)
    have hb := (RAMBoundary.checks_iff (Nat.two_pow_pos h) (sortedBlock h d x) m.lastRecords).mp
      (fun v => by change RAMBoundary.checkAt _ _ _ _; rw [← hout v]; exact (hm v).2)
    refine ⟨MemoryMessages.ext ?_ hb.2, hb.1⟩
    apply (physicalFieldsEquiv.{0,0} h d _).injective
    change _ = (physicalFieldsEquiv.{0,0} h d _) ((physicalFieldsEquiv.{0,0} h d _).symm _)
    rw [Equiv.apply_symm_apply]
    exact fields_eq_actual _ _ x hc
  · rintro ⟨rfl, hb⟩
    let msg := actualMemoryMessages h d x
    have hc (v) : checks v (schedule h d) (physicalFieldsEquiv.{0,0} h d _ msg.sortSends)
        (block h v.val x) := by
      change checks v _ ((physicalFieldsEquiv.{0,0} h d _) ((physicalFieldsEquiv.{0,0} h d _).symm _)) _
      rw [Equiv.apply_symm_apply]
      exact checks_actual ..
    intro v
    refine ⟨hc v, ?_⟩
    have hout : outputAt msg v (block h v.val x) = sortedBlock h d x v := by
      funext i
      exact congrArg (fun f : Wires h (OrderedSlot (Word w)) => (f i).record)
        (replay_phases _ x hc v)
    change RAMBoundary.checkAt _ _ _ (outputAt msg v _)
    rw [hout]
    exact (RAMBoundary.checks_iff _ _ _).mpr ⟨hb, rfl⟩ v

/-- The memory transcript for the actual RAM record blocks. -/
theorem report_memoryAt_iff (header : ℕ → Word w) {d e : ℕ} {rs : List (Report w)}
    (hcap : RAMBuckets.cost Report.probes rs ≤ 2^d * 2^e)
    (hc : ∀ r ∈ rs, 1 + r.probes ≤ 2^e) (m : MemoryMessages (2+e) d w) :
    (∀ v, MemoryAt m v (block (2+e) v.val (recordWires header d e rs))) ↔
      m = actualMemoryMessages (2+e) d (recordWires header d e rs) ∧
      Correct (initialMemory (2^d) header) (rs.map Report.events).flatten := by
  rw [memoryAt_iff, ← sortedRecords_read_check header hcap hc]
  have hflat : RAMBoundary.flat (sortedBlock (2+e) d (recordWires header d e rs)) =
      sortedRecords header d e rs := by
    let x := runPhases ((2+e)+d) (recordWires header d e rs)
    have he := flatten_ofFn_blocks (2+e) d (fun i => (x i).record)
    unfold sortedRecords
    rw [List.map_ofFn]
    exact he
  rw [hflat]

end BurstRAM

end VPVNP
end Computability
end OAI
