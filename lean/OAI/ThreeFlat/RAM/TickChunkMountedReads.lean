import OAI.ThreeFlat.RAM.TickChunkReads

namespace OAI
/-! # Reading physical endpoint pins after the interval cursor -/

namespace ThreeFlat.RAM.TickChunkCheck

open Computability.VPVNP.BurstRAM TickIntervalCursor Diagonal.TickGroupIntervals ChunkRequests TickBitRelation
open scoped Fin.CommRing

variable {w : ℕ}

theorem pairReads_of_layout (m : Memory w) (start : ℕ) (L : Layout) (es : List Interval)
    (ptr base n : ℕ) (bits : ℕ → Bool) (ptrFit : ptr < 2^w) (dataFit : base+n ≤ 2^w)
    (cache : m ptr = (base : Word w)) (validCode : ∀ i : Fin (chunkSize L), codeAt L es i.val ≤ n)
    (stored : ∀ j < n, m (base+j) = bitWord w (bits j))
    (cacheMap : ptr < L.mapBase ∨ L.mapBase+chunkSize L ≤ ptr)
    (cacheScratch : outside start (chunkSize L) ptr)
    (dataMap : ∀ j < n, base+j < L.mapBase ∨ L.mapBase+chunkSize L ≤ base+j)
    (dataScratch : ∀ j < n, outside start (chunkSize L) (base+j)) :
    PairReads (output L m es) start L es ptr bits := by
  have pc : (ptr : Word w).val = ptr := Fin.val_cast_of_lt ptrFit
  have loaded : output L m es (ptr : Word w).val = (base : Word w) := by
    rw [pc,output_outside L m es ptr cacheMap,cache]
  have addr (i : Fin (chunkSize L)) (live : codeAt L es i.val ≠ 0) :
      (output L m es (ptr : Word w).val + ((codeAt L es i.val : Word w)-1)).val =
        base+(codeAt L es i.val-1) := by
    have positive : 1 ≤ codeAt L es i.val := by omega
    have sub : ((codeAt L es i.val-1 : ℕ) : Word w) = (codeAt L es i.val : Word w)-1 := by
      rw [Nat.cast_sub positive,Nat.cast_one]
    rw [loaded,← sub,← Nat.cast_add]
    exact Fin.val_cast_of_lt (by have := validCode i; omega)
  refine ⟨by simpa only [pc] using cacheScratch,?_,?_⟩
  · intro i live
    rw [addr i live]
    exact dataScratch _ (by have := validCode i; omega)
  · intro i live
    rw [addr i live]
    have ix : codeAt L es i.val-1 < n := by have := validCode i; omega
    rw [output_outside L m es _ (dataMap _ ix),stored _ ix]

theorem read_pin (m : Memory w) (L : Layout) (es : List Interval) (base : ℕ)
    (pins : Fin (chunkSize L) → Bool) (fit : base+chunkSize L ≤ 2^w)
    (separate : ∀ i : Fin (chunkSize L), base+i.val < L.mapBase ∨ L.mapBase+chunkSize L ≤ base+i.val)
    (reads : ∀ i : Fin (chunkSize L), m (base+i.val) = bitWord w (pins i)) (i : Fin (chunkSize L)) :
    bitAt (output L m es) (base : Word w) (i.val : Word w) = bitWord w (pins i) := by
  unfold bitAt
  rw [← Nat.cast_add,Fin.val_cast_of_lt (show base+i.val < 2^w by omega),
    output_outside L m es _ (separate i),reads i]


end ThreeFlat.RAM.TickChunkCheck

end OAI
