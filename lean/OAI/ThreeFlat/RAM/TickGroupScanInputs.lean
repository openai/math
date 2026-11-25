import OAI.ThreeFlat.RAM.TickGroupScanBank
import OAI.ThreeFlat.RAM.TickChunkMountedReads
import OAI.ThreeFlat.RAM.TickScanColumns

namespace OAI
/-! # The native history scan from the naturally addressed navigator cache -/

namespace ThreeFlat.RAM.TickGroupScanBank

open Computability.VPVNP.BurstRAM TickIntervalCursor Diagonal.TickGroupIntervals TickChunkCheck ChunkRequests TickBitRelation
open scoped Fin.CommRing

/-- Address order on this ABI places the request stream in S4, the interval
rows in S5, the count in S6, and the zero-initialized dense map in S7.
Both pair pointers and the mounted endpoint words precede S4. -/
theorem ScanInputs.of_ranges {w : ℕ} (A : Plan) (es : List Interval) (lo g : ℕ)
    (m : Memory w) (op np : ℕ → Bool) (x y : Fin (chunkSize (layout A lo g)) → Bool)
    (n oldPairBase newPairBase : ℕ) (disj : es.Pairwise Compatible)
    (width : 64 ≤ 2^w) (chunkFit : lo+A.bits < 2^w) (groupFit : g < 2^w)
    (requestBeforeTable : A.reqStart+8*A.bits ≤ A.table)
    (tableBeforeMap : A.table+4*es.length ≤ A.mapBase) (mapFit : A.mapBase+A.bits < 2^w)
    (caches : A.countAddr < A.mapBase ∧ A.chunkAddr < A.mapBase ∧ A.groupAddr < A.mapBase)
    (nread : m A.countAddr = (es.length : Word w)) (lread : m A.chunkAddr = (lo : Word w))
    (gread : m A.groupAddr = (g : Word w))
    (good : ∀ e ∈ es, FitsRow e w) (stored : Stores m A.table es)
    (zeros : ∀ j < A.bits, m (A.mapBase+j) = 0)
    (codeBound : ∀ i : Fin (chunkSize (layout A lo g)), codeAt (layout A lo g) es i.val ≤ n)
    (ptrs : A.oldPtr < A.reqStart ∧ A.newPtr < A.reqStart)
    (pairEnd : oldPairBase+n ≤ A.reqStart ∧ newPairBase+n ≤ A.reqStart)
    (oldCache : m A.oldPtr = (oldPairBase : Word w)) (newCache : m A.newPtr = (newPairBase : Word w))
    (oldData : ∀ j < n, m (oldPairBase+j) = bitWord w (op j))
    (newData : ∀ j < n, m (newPairBase+j) = bitWord w (np j))
    (pins : A.old+A.bits ≤ A.reqStart ∧ A.new+A.bits ≤ A.reqStart)
    (oldPin : ∀ i : Fin (chunkSize (layout A lo g)), m (A.old+i.val) = bitWord w (x i))
    (newPin : ∀ i : Fin (chunkSize (layout A lo g)), m (A.new+i.val) = bitWord w (y i)) :
    ScanInputs w A es lo g m op np x y := by
  let L := layout A lo g
  have len : chunkSize L = A.bits := size A lo g
  have map : L.mapBase = A.mapBase := rfl
  have before : A.reqStart ≤ A.mapBase := by omega
  have room : A.reqStart < 2^w := by omega
  have val (k : ℕ) (hk : k < 2^w) : (k : Word w).val = k := Fin.val_cast_of_lt hk
  have addr (base : ℕ) (s : base+A.bits ≤ 2^w) (i : Fin (chunkSize L)) :
      ((base : Word w)+(i.val : Word w)).val = base+i.val := by
    rw [← Nat.cast_add,val _ (by have := i.isLt; omega)]
  have pair (ptr base : ℕ) (bits : ℕ → Bool) (hp : ptr < A.reqStart)
      (hb : base+n ≤ A.reqStart) (cached : m ptr = (base : Word w))
      (st : ∀ j < n, m (base+j) = bitWord w (bits j)) :
      PairReads (output L m es) A.reqStart L es ptr bits :=
    pairReads_of_layout m A.reqStart L es ptr base n bits (by omega) (by omega) cached codeBound st
      (Or.inl (by omega)) (Or.inl hp) (fun _ hj => Or.inl (by omega)) (fun _ hj => Or.inl (by omega))
  have read (base : ℕ) (bits : Fin (chunkSize L) → Bool) (hb : base+A.bits ≤ A.reqStart)
      (rd : ∀ i : Fin (chunkSize L), m (base+i.val) = bitWord w (bits i)) :
      ∀ i : Fin (chunkSize L), bitAt (output L m es) (base : Word w) (i.val : Word w) = bitWord w (bits i) :=
    read_pin m L es base bits (by omega) (fun i => Or.inl (by have := i.isLt; omega)) rd
  refine ⟨disj,?_,?_,?_,?_,width,by omega,by omega,good,stored,?_,zeros,?_,?_,
    pair _ _ _ ptrs.1 pairEnd.1 oldCache oldData,pair _ _ _ ptrs.2 pairEnd.2 newCache newData,
    ?_,?_,read _ _ pins.1 oldPin,read _ _ pins.2 newPin⟩
  · rwa [val _ (by omega)]
  · rwa [val _ (by omega)]
  · rwa [val _ (by omega)]
  · refine ⟨by change lo ≤ lo+A.bits; omega,chunkFit,?_,groupFit⟩
    change A.mapBase+(lo+A.bits-lo) < 2^w
    simpa only [Nat.add_sub_cancel_left] using mapFit
  · intro k hk ht
    exact Or.inl (by omega)
  · intro i
    have := codeBound i
    omega
  · intro i
    rw [addr A.mapBase (by omega) i]
    exact Or.inr (by omega)
  · intro i
    rw [addr A.old (by omega) i]
    have hi := i.isLt
    change i.val < chunkSize L at hi
    omega
  · intro i
    rw [addr A.new (by omega) i]
    have hi := i.isLt
    change i.val < chunkSize L at hi
    omega


end ThreeFlat.RAM.TickGroupScanBank

end OAI
