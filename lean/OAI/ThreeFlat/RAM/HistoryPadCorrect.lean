import OAI.ThreeFlat.RAM.HistoryPadScan
import OAI.ThreeFlat.RAM.HistoryFactorPadding

namespace OAI
/-! # Compact four-word records emitted by the native padding descriptor -/

namespace ThreeFlat.RAM.HistoryFactors

open Computability.VPVNP.BurstRAM Diagonal.TraceCircuit BitLayout HistoryPadScan Fin.CommRing
variable {F : Type*} [Zero F] [One F] {p w k : ℕ}

/-- The first three columns encode resolved addresses and the fourth encodes a table ID. -/
def metadataWord {N : BitNetwork F p} (L : Library N) (i : Fin N.cells) (j : Fin 4) : Word w :=
  if h : j.val < 3 then Fin.ofNat _ (sourceAddress (N.source i ⟨j.val,h⟩))
  else Fin.ofNat _ (L.id i).val

/-- A genuine compact record retains all its absolute source addresses and its tag. -/
theorem metadataWord_original {N : BitNetwork F p} (L : Library N) (b u : ℕ)
    (i : Fin N.cells) (j : Fin 4) : metadataWord (w := w) (L.padded b u)
      ((i.castAdd b).castAdd u) j = metadataWord L i j := by
  by_cases h : j.val < 3
  · simp only [metadataWord, dite_eq_left h, addPadding, Fin.addCases_left, networkCells, Cell.lift]
    cases N.source i ⟨j.val,h⟩ <;> rfl
  · simp [metadataWord, h, Library.padded]

/-- Index in the padded network of zero-based suffix row t. -/
def suffixIndex (n b u : ℕ) : Fin (b+u) → Fin ((n+b)+u) :=
  Fin.addCases (fun i => (Fin.natAdd n i).castAdd u) (Fin.natAdd (n+b))

theorem suffixIndex_val (n b u : ℕ) (i : Fin (b+u)) :
    (suffixIndex n b u i).val = n+i.val := by
  refine Fin.addCases (fun t => ?_) (fun t => ?_) i
  · simp [suffixIndex]
  · simp [suffixIndex, Nat.add_assoc]

private theorem zero_record {N : BitNetwork F p} (L : Library N) (b u : ℕ) (i : Fin b)
    (j : Fin 4) : metadataWord (w := w) (L.padded b u) ((Fin.natAdd N.cells i).castAdd u) j =
      if j.val = 3 then (L.count : Word w)
      else if j.val = 0 then ((hiddenBase p+N.internal : ℕ) : Word w)+(i.val : Word w) else 0 := by
  fin_cases j <;> simp only [metadataWord, addPadding, Library.padded, Fin.addCases_left,
    Fin.addCases_right] <;> first | rfl | (change
      ((hiddenBase p + (N.internal + i.val) : ℕ) : Word w) =
        ((hiddenBase p+N.internal : ℕ) : Word w)+(i.val : Word w); rw [← Nat.cast_add, Nat.add_assoc])

private theorem unit_record {N : BitNetwork F p} (L : Library N) (b u : ℕ) (i : Fin u)
    (j : Fin 4) : metadataWord (w := w) (L.padded b u) (Fin.natAdd (N.cells+b) i) j =
      if j.val = 3 then (L.count : Word w)+1 else 0 := by
  fin_cases j <;> simp only [metadataWord, addPadding, Library.padded, Fin.addCases_right]
    <;> first | rfl | (change ((L.count+1 : ℕ) : Word w) = (L.count : Word w)+1; simp)

/-- For every suffix position, the native arithmetic descriptor returns precisely its
semantic padded word. A controller writes it after the genuine compact metadata prefix. -/
theorem padTailWord_eq {N : BitNetwork F p} (L : Library N) (b u : ℕ)
    (i : Fin (b+u)) (j : Fin 4) (data : Fin k → Word w) (m : Memory w)
    (hw : 4 < 2^w) (hof : 4*i.val+j.val < 2^w) (hb : b < 2^w) :
    padTailWord.eval data m ![((4*i.val+j.val : ℕ) : Word w), (b : Word w),
        ((hiddenBase p+N.internal : ℕ) : Word w), (L.count : Word w)] =
      metadataWord (L.padded b u) (suffixIndex N.cells b u i) j := by
  rw [eval_padTailWord]
  change padWord ((4*i.val+j.val : ℕ) : Word w) (b : Word w)
    ((hiddenBase p+N.internal : ℕ) : Word w) (L.count : Word w) = _
  refine (padWord_at i.val b j _ _ hw hof hb).trans ?_
  refine Fin.addCases (fun t => ?_) (fun t => ?_) i
  · simpa [suffixIndex, t.isLt] using (zero_record (w:=w) L b u t j).symm
  · simpa [suffixIndex] using (unit_record (w:=w) L b u t j).symm

end ThreeFlat.RAM.HistoryFactors

end OAI
