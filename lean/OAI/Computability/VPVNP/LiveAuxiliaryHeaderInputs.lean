import OAI.Computability.VPVNP.LiveAuxiliaryHeaderSweep

/-!
# Linking the seven input arrays to the auxiliary coefficient machine

The sparse writer reads one word per length, primed index bit, advice bit,
exterior bit, and nominated histogram entry. The field equations below
are the contracts provided by their individual producer routines.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveAuxiliaryHeaders

open BurstRAM PrimedInputRAM LiveHeaderCopyDispatch
open scoped Fin.CommRing

variable {w : ℕ}

/-- The seven field lengths in copy order, covering the three length words, both index fields,
advice, exterior cuts, and nominated histogram. -/
def fieldSize (L : Lengths) (N : ℕ) : Fin 7 → ℕ :=
  ![3,L.index,L.index,L.advice,L.leftCut,L.rightCut,N]

private theorem field_end (L : Lengths) (N : ℕ) (f : Fin 7) :
    rangeStart L N f.castSucc + fieldSize L N f = rangeStart L N f.succ := by
  fin_cases f <;> simp [rangeStart, fieldSize, exteriorBase]
  omega

private def atWord (m : Memory w) (base : Word w) (offset : ℕ) := m (base + (offset : Word w)).val

/-- Memory equations for the producer outputs, before writing the sparse O header. -/
structure InputArrays (L : Lengths) (hdr : Header L → Bool) (hist : List (Word w))
    (source : Fin 7 → Word w) (m : Memory w) : Prop where
  lengths : ∀ j : Fin 3, m (source 0 + (j.val : Word w)).val = Fin.ofNat _ (cutLength L j)
  leftIndex : ∀ j : Fin L.index, m (source 1 + (j.val : Word w)).val = encodeBit w (hdr (.group 0 j))
  rightIndex : ∀ j : Fin L.index, m (source 2 + (j.val : Word w)).val = encodeBit w (hdr (.group 1 j))
  advice : ∀ j : Fin L.advice, m (source 3 + (j.val : Word w)).val = encodeBit w (hdr (.advice j))
  leftCut : ∀ j : Fin L.leftCut, m (source 4 + (j.val : Word w)).val = encodeBit w (hdr (.leftCut j))
  rightCut : ∀ j : Fin L.rightCut, m (source 5 + (j.val : Word w)).val = encodeBit w (hdr (.rightCut j))
  nominations : ∀ j : Fin hist.length, m (source 6 + (j.val : Word w)).val = hist[j]

variable {L : Lengths} {hdr : Header L → Bool} {hist : List (Word w)}
    {src : Fin 7 → Word w} {m : Memory w}

private theorem InputArrays.field (ha : InputArrays L hdr hist src m) (f : Fin 7)
    (j : Fin (fieldSize L hist.length f)) :
    atWord m (src f) j.val = headerMemory L hdr hist (destinationStart L f + j.val) := by
  fin_cases f
  · simpa [atWord, destinationStart, headerMemory_length L hdr hist j] using ha.lengths j
  · exact (ha.leftIndex j).trans (by
      simpa [destinationStart, Header.address] using (headerMemory_bits L hdr hist (.group 0 j)).symm)
  · exact (ha.rightIndex j).trans (by
      simpa [destinationStart, Header.address] using (headerMemory_bits L hdr hist (.group 1 j)).symm)
  · exact (ha.advice j).trans (headerMemory_bits L hdr hist (.advice j)).symm
  · exact (ha.leftCut j).trans (headerMemory_bits L hdr hist (.leftCut j)).symm
  · exact (ha.rightCut j).trans (headerMemory_bits L hdr hist (.rightCut j)).symm
  · change atWord m (src 6) j.val = headerMemory L hdr hist (Header.count L + j.val)
    rw [headerMemory_hist, List.getElem?_eq_getElem (by exact j.isLt), Option.getD_some]
    exact ha.nominations ⟨j.val, j.isLt⟩

/-- Every packed read lands on its producer's word and every destination is
the address the auxiliary machine will query for that field. -/
theorem InputArrays.read (ha : InputArrays L hdr hist src m) (i : Fin (populated L hist.length)) :
    m (sourceAddress L hist.length src i).val = headerMemory L hdr hist (sparseOffset L hist.length i).val := by
  let f := rangeAt L hist.length i
  let k := i.val - rangeStart L hist.length f.castSucc
  have hlo : rangeStart L hist.length f.castSucc ≤ i.val := (rangeAt_bounds L hist.length i).1
  have hi : i.val < rangeStart L hist.length f.castSucc + fieldSize L hist.length f := by
    rw [field_end]; exact (rangeAt_bounds L hist.length i).2
  have hk : k < fieldSize L hist.length f := by dsimp [k]; omega
  rw [sparseOffset_at_range]
  exact ha.field f ⟨k,hk⟩

theorem InputArrays.prepared (ha : InputArrays L hdr hist src m) {desc : Word w} {base : ℕ}
    (ht : Spec desc (records L hist.length base src) m) : Prepared desc base L hdr hist src m :=
  ⟨ht, ha.read⟩

end LiveAuxiliaryHeaders

end VPVNP
end Computability
end OAI
