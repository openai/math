import OAI.ThreeFlat.RAM.TickIntervalScan
import OAI.ThreeFlat.Diagonal.HistoryBucketRows
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Interpreting the four native S5 words for each navigation interval -/

namespace ThreeFlat.RAM.TickIntervalCursor

open Computability.VPVNP.BurstRAM Diagonal.TickGroupIntervals Diagonal.HistoryContraction
open scoped Fin.CommRing

def intervalColumn (e : Interval) : Fin 4 → ℕ := ![e.group,e.first,e.stop,e.packed]

theorem stores_of_columns {w n : ℕ} (m : Memory w) (base : ℕ) (es : Fin n → Interval)
    (read : ∀ i : Fin n, ∀ j : Fin 4, m (base+4*i.val+j.val) = (intervalColumn (es i) j : Word w)) :
    Stores m base (List.ofFn es) := by
  induction n generalizing base with
  | zero => simp [Stores]
  | succ n ih =>
    rw [List.ofFn_succ]
    constructor
    · have head (j : Fin 4) : m (base+j.val) = (intervalColumn (es 0) j : Word w) := by
        simpa only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] using read 0 j
      have first : m base = (intervalColumn (es 0) 0 : Word w) := by
        simpa only [Fin.val_zero,Nat.add_zero] using head 0
      exact ⟨first,head 1,head 2,head 3⟩
    · apply ih (base+4) (fun i => es i.succ)
      intro i j
      have addr : base+4*i.succ.val+j.val = (base+4)+4*i.val+j.val := by
        simp only [Fin.val_succ]
        omega
      simpa only [addr] using read i.succ j

def bucketInterval {d : ℕ} (r : BucketRow (Fin d)) : Interval := ⟨r.group.val,r.lo,r.hi,r.offset⟩

/-- This accepts the native four-column output of the original bucket emitter
directly. The counter address can be anywhere disjoint from the row area. -/
theorem stores_of_bucket_columns {w n d : ℕ} (m : Memory w) (base : ℕ) (rs : Fin n → BucketRow (Fin d))
    (read : ∀ i : Fin n, ∀ j : Fin 4,
      m (base+4*i.val+j.val) = ((![((rs i).group.val),(rs i).lo,(rs i).hi,(rs i).offset] j : ℕ) : Word w)) :
    Stores m base (List.ofFn fun i => bucketInterval (rs i)) :=
  stores_of_columns m base _ read

end ThreeFlat.RAM.TickIntervalCursor

end OAI
