import OAI.ThreeFlat.RAM.HistoryPadDriver
import OAI.ThreeFlat.RAM.HistoryPadCorrect

namespace OAI
/-! # The padded metadata and LUT frame at the native sweep exit -/

namespace ThreeFlat.RAM.HistoryPadDriver

open Computability.VPVNP.BurstRAM BitLayout HistoryPadScan HistoryFactors Diagonal.TraceCircuit Fin.CommRing

variable {F : Type*} [Zero F] [One F] {p w : ℕ}

/-- The physical output of the variable-length metadata sweep. -/
def paddedMemory {N : BitNetwork F p} (L : Library N) (b u metadata : ℕ)
    (input : Memory w) : Memory w :=
  let lo := metadata+4*N.cells
  fillSegment lo (4*(b+u)) (word lo (b : Word w) ((hiddenBase p+N.internal : ℕ) : Word w)
    (L.count : Word w)) input

private theorem suffix_read {N : BitNetwork F p} (L : Library N) (b u metadata : ℕ)
    (m : Memory w) (fit : metadata+4*N.cells+4*(b+u) < 2^w) (t : Fin (b+u)) (j : Fin 4) :
    paddedMemory L b u metadata m (metadata+4*(suffixIndex N.cells b u t).val+j.val) =
      metadataWord (L.padded b u) (suffixIndex N.cells b u t) j := by
  let lo := metadata+4*N.cells
  have ht := t.isLt
  have hj := j.isLt
  have range : lo ≤ lo+(4*t.val+j.val) ∧ lo+(4*t.val+j.val) < lo+4*(b+u) := by omega
  have addr : metadata+4*(suffixIndex N.cells b u t).val+j.val = lo+(4*t.val+j.val) := by
    rw [suffixIndex_val]
    dsimp [lo]
    omega
  rw [addr]
  change fillSegment lo _ _ _ (lo+(4*t.val+j.val)) = _
  rw [fillSegment,ite_eq_left range]
  have result := padTailWord_eq (w:=w) L b u t j (Fin.elim0 : Fin 0 → Word w) m
    (by omega) (by omega) (by omega)
  rw [eval_padTailWord] at result
  change padWord ((4*t.val+j.val : ℕ) : Word w) (b : Word w)
    ((hiddenBase p+N.internal : ℕ) : Word w) (L.count : Word w) = _ at result
  simpa only [word,lo,Nat.cast_add,add_sub_cancel_left] using result

/-- The prior genuine rows stay live, each appended row is generated from its actual
runtime position, and the read-only shared library lies beyond the destination interval. -/
theorem stores_after_padding {N : BitNetwork F p} (L : Library N) (b u metadata lut : ℕ)
    (code : FieldCode F w) (input : Memory w) (fit : metadata+4*N.cells+4*(b+u) < 2^w)
    (afterLut : metadata+4*N.cells+4*(b+u) ≤ lut)
    (genuine : ∀ i : Fin N.cells, ∀ j : Fin 4,
      input (metadata+4*i.val+j.val) = metadataWord L i j)
    (tables : ∀ t : Fin (L.count+2), ∀ j : Fin 8,
      input (lut+8*t.val+j.val) = code.encode ((L.padded b u).table t (bits j.val))) :
    Stores (addPadding N b u) (L.padded b u) code metadata lut (paddedMemory L b u metadata input) := by
  let m := paddedMemory L b u metadata input
  have allRows (i : Fin ((N.cells+b)+u)) (j : Fin 4) :
      m (metadata+4*i.val+j.val) = metadataWord (L.padded b u) i j := by
    refine Fin.addCases (fun x : Fin (N.cells+b) => ?_) (fun x : Fin u => ?_) i
    · refine Fin.addCases (fun a : Fin N.cells => ?_) (fun a : Fin b => ?_) x
      · rw [metadataWord_original]
        have ha := a.isLt
        have hj := j.isLt
        have low : metadata+4*a.val+j.val < metadata+4*N.cells := by omega
        change fillSegment _ _ _ input (metadata+4*a.val+j.val) = _
        rw [fillSegment,ite_eq_right (fun h => (Nat.not_le.mpr low) h.1)]
        exact genuine a j
      · simpa only [suffixIndex,Fin.addCases_left] using suffix_read L b u metadata input fit (a.castAdd u) j
    · simpa only [suffixIndex,Fin.addCases_right] using suffix_read L b u metadata input fit (Fin.natAdd b x) j
  constructor
  · intro i j
    simpa [metadataWord,j.isLt] using allRows i j.castSucc
  · intro i
    simpa [metadataWord] using allRows i (3 : Fin 4)
  · intro t j
    have away : metadata+4*N.cells+4*(b+u) ≤ lut+8*t.val+j.val := by omega
    change fillSegment _ _ _ input (lut+8*t.val+j.val) = _
    rw [fillSegment,ite_eq_right (fun h => (Nat.not_lt.mpr away) h.2)]
    exact tables t j

end ThreeFlat.RAM.HistoryPadDriver

end OAI
