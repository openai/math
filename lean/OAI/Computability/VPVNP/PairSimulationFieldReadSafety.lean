import OAI.Computability.VPVNP.PairSimulationSliceReads
import OAI.Computability.VPVNP.PairSimulationTerminalSplice
import OAI.Computability.VPVNP.PairSimulationRefreshSliceClock
import OAI.Computability.VPVNP.CompressorSliceIndexedStarts

/-!
# Field traces below the terminal header

External reads confined below the allocated terminal header exclude its stage and
saved-state cells. The two slice formats locate their length and offsets at different
addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation

open BurstRAM CompressorRecords CompressorRecords.PhaseRecipe CompressorRecords.SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} {data : ℕ → Prop}

/-- All addresses below a fitting terminal header avoid the stage cell and saved word. -/
theorem TerminalLink.workerCell_of_lt {H : Word w} (fit : H.val + 31 < 2 ^ w)
    {i : ℕ} (below : i < H.val) : TerminalLink.workerCell H i := by
  have last : (H + 31).val = H.val + 31 := by
    rw [Fin.val_add, show (31 : Word w) = ((31 : ℕ) : Word w) from rfl, Fin.val_natCast,
      Nat.mod_eq_of_lt (by omega : 31 < 2 ^ w), Nat.mod_eq_of_lt fit]
  exact ⟨below.ne, by rw [last]; omega⟩

/-- Register formulas whose loads all precede the terminal header read worker cells. -/
theorem TerminalLink.expr_worker_reads {H : Word w} (fit : H.val + 31 < 2 ^ w)
    {pub : Fin 5 → Word w} {state : Word w} {mem : Memory w} {e : Expr}
    (allowed : e.ReadsFrom (· < H.val) pub state mem) :
    e.ReadsFrom (TerminalLink.workerCell H) pub state mem :=
  allowed.mono fun _ hi => TerminalLink.workerCell_of_lt fit hi

/-- A natural frame head and its two successors all lie below the terminal header. -/
theorem PrivateSlices.frameEvents_worker_reads {H : Word w} (fit : H.val + 31 < 2 ^ w)
    (m : Memory w) (head : ℕ) (bs : List Bool) (before : head + 2 < H.val) :
    Reads (TerminalLink.workerCell H) (PrivateSlices.frameEvents m (head : Word w) bs) := by
  have bound := before.trans H.isLt
  have a₀ : (head : Word w).val = head := Nat.mod_eq_of_lt (by omega)
  have a₁ : ((head : Word w) + 1).val = head + 1 := by
    rw [← Nat.cast_add_one]
    exact Nat.mod_eq_of_lt (by omega)
  have a₂ : ((head : Word w) + 1 + 1).val = head + 2 := by
    rw [← Nat.cast_add_one, ← Nat.cast_add_one]
    exact Nat.mod_eq_of_lt bound
  apply PrivateSlices.frameEvents_reads <;> apply TerminalLink.workerCell_of_lt fit <;> omega

/-- Source-major indexing puts the three cells of any AB frame strictly inside
the allocated interval bank for its bundle. -/
theorem PrivateSlices.ab_frame_before {bank H m n : ℕ} (source : Fin m) (target : Fin n)
    (before : bank + IndexedStarts.capacity m n ≤ H) :
    bank + m + n + 3 * (source.val * n + target.val) + 2 < H := by
  have idx : source.val * n + target.val < m * n := calc
    _ < source.val * n + n := Nat.add_lt_add_left target.isLt _
    _ = (source.val + 1) * n := (Nat.succ_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right n source.isLt
  unfold IndexedStarts.capacity at before
  omega

/-- The surviving row holds one frame per subdivision, preceding its directory
references in the same allocated bank. -/
theorem PrivateSlices.surviving_frame_before {bank H q : ℕ} (j : Fin q)
    (before : SliceSchedule.stop bank 1 q ≤ H) :
    SliceSchedule.frameHead bank 1 q + 3 * j.val + 2 < H := by
  simp only [SliceSchedule.stop, one_mul] at before
  have := j.isLt
  omega

/-- The two reads of a refresh segment use the selected width and offset column heads
at its physical ordinal. -/
theorem RefreshSliceClock.segmentEvents_reads_iff (m : Memory w) (width offset ordinal : Word w)
    (bs : List Bool) :
    Reads data (RefreshSliceClock.segmentEvents m width offset ordinal bs) ↔
      data (width + ordinal).val ∧ data (offset + ordinal).val := by
  have header : Reads data (RefreshSliceClock.segmentEvents m width offset ordinal bs) ↔
      Reads data (RefreshSliceClock.headerEvents m width offset ordinal) := by
    constructor
    · exact fun h a v hv => h a v (List.mem_append_left _ hv)
    · intro h a v hv
      exact (List.mem_append.mp hv).elim (h a v) (PrivateFields.events_reads .copy bs a v)
  rw [header]
  simp [RefreshSliceClock.headerEvents, Reads, or_imp, forall_and]

/-- All segments in two allocated refresh columns precede the terminal controls.
The bound uses the ordinal within the columns, including at their last cell. -/
theorem RefreshSliceClock.segmentEvents_worker_reads {H : Word w} (fit : H.val + 31 < 2 ^ w)
    (m : Memory w) (width offset ordinal : Word w) (bs : List Bool) {n : ℕ} (idx : ordinal.val < n)
    (widthBefore : width.val + n ≤ H.val) (offsetBefore : offset.val + n ≤ H.val) :
    Reads (TerminalLink.workerCell H)
      (RefreshSliceClock.segmentEvents m width offset ordinal bs) := by
  rw [RefreshSliceClock.segmentEvents_reads_iff]
  have below (base : Word w) (bound : base.val + n ≤ H.val) : (base + ordinal).val < H.val := by
    have h := (Nat.add_lt_add_left idx base.val).trans_le bound
    rwa [Fin.val_add, Nat.mod_eq_of_lt (h.trans H.isLt)]
  exact ⟨TerminalLink.workerCell_of_lt fit (below width widthBefore),
    TerminalLink.workerCell_of_lt fit (below offset offsetBefore)⟩

end PairSimulation

end VPVNP
end Computability
end OAI
