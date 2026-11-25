import OAI.ThreeFlat.RAM.TickChunkPredicate
import OAI.ThreeFlat.RAM.TickIntervalScan
import OAI.ThreeFlat.RAM.TickBitRelation
import OAI.ThreeFlat.RAM.ExpressionScan

namespace OAI
/-! # Word addresses and pair values read from the interval map -/

namespace ThreeFlat.RAM.TickChunkCheck

open Computability.VPVNP.BurstRAM DescriptorScan Diagonal.TickGroupIntervals TickIntervalCursor TickBitRelation
open scoped Fin.CommRing

def outside (start size addr : ℕ) : Prop := addr < start ∨ start+8*size ≤ addr

/-- The pair pointers and any pair words addressed by a live map entry are
read from the interval cursor's output memory. The request stream is disjoint
from these reads. -/
structure PairReads {w : ℕ} (m : Memory w) (start : ℕ) (L : Layout) (es : List Interval)
    (ptr : ℕ) (bits : ℕ → Bool) : Prop where
  ptr_safe : outside start (chunkSize L) (ptr : Word w).val
  data_safe : ∀ i : Fin (chunkSize L), codeAt L es i.val ≠ 0 →
    outside start (chunkSize L) (m (ptr : Word w).val + ((codeAt L es i.val : Word w)-1)).val
  read : ∀ i : Fin (chunkSize L), codeAt L es i.val ≠ 0 →
    m (m (ptr : Word w).val + ((codeAt L es i.val : Word w)-1)).val =
      bitWord w (bits (codeAt L es i.val-1))

theorem pairRead {w : ℕ} {m m' : Memory w} {start : ℕ} {L : Layout} {es : List Interval}
    {ptr : ℕ} {bits : ℕ → Bool} (h : PairReads m start L es ptr bits)
    (same : agreesOutside start (start+8*chunkSize L) m' m) (i : Fin (chunkSize L))
    (live : codeAt L es i.val ≠ 0) :
    m' (m' (ptr : Word w).val+((codeAt L es i.val : Word w)-1)).val =
      bitWord w (bits (codeAt L es i.val-1)) := by
  rw [same _ h.ptr_safe,same _ (h.data_safe i live),h.read i live]

theorem read_code {w : ℕ} (L : Layout) (fit : L.Fits w) (es : List Interval)
    (disj : es.Pairwise Compatible) (m : Memory w)
    (zero : ∀ j < chunkSize L, m (L.mapBase+j) = 0) (i : Fin (chunkSize L)) :
    output L m es ((L.mapBase : Word w)+(i.val : Word w)).val = (codeAt L es i.val : Word w) := by
  have hi := i.isLt
  have map := fit.map
  unfold chunkSize at hi
  have haddr : ((L.mapBase : Word w)+(i.val : Word w)).val = L.mapBase+i.val := by
    rw [← Nat.cast_add,Fin.val_cast_of_lt (by omega : L.mapBase+i.val < 2^w)]
  rw [haddr]
  simpa only [codeAt,Nat.add_sub_cancel_left] using
    output_zeroMap L m es disj zero (x:=L.chunkStart+i.val) (by omega) (by omega)

end ThreeFlat.RAM.TickChunkCheck

end OAI
