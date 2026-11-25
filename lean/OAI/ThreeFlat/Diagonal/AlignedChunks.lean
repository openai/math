import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Fin

namespace OAI
/-! # Constant-operation chunk addresses in aligned blocks

The chunks of a half are indexed by a block number followed by the low
tick-within-block index. Integer division selects the first index.
-/

namespace ThreeFlat.Diagonal.AlignedChunks

variable {period width : ℕ}

/-- The phase within one half cycles once per full scan of both halves. -/
def phase (period block : ℕ) [NeZero period] : Fin period := Fin.ofNat period block

def active (period block : ℕ) : Bool := (block / period).testBit 0

def slot (row : Fin period) (low : Fin width) : Fin (period*width) :=
  finProdFinEquiv (row,low)

def keep (row : Fin period) (chunk : Fin (period*width)) : Bool :=
  decide ((finProdFinEquiv.symm chunk).1 ≠ row)

theorem slot_injective (row : Fin period) : Function.Injective (slot (width := width) row) := by
  intro i j h
  exact (Prod.mk.inj (finProdFinEquiv.injective h)).2

theorem keep_spec (row : Fin period) (chunk : Fin (period*width)) :
    keep row chunk = true ↔ chunk ∉ Finset.univ.image (slot row) := by
  obtain ⟨⟨hi,lo⟩,rfl⟩ := finProdFinEquiv.surjective chunk
  simp [keep, slot]
  exact not_congr eq_comm

theorem slot_nat (row : Fin period) (low : Fin width) :
    (slot row low).val = row.val*width+low.val := by
  change low.val + width * row.val = _
  ac_rfl

theorem keep_nat (row : Fin period) (chunk : Fin (period*width)) :
    keep row chunk = decide (chunk.val / width ≠ row.val) := by
  simp only [keep, ne_eq, Fin.ext_iff]
  rfl

end ThreeFlat.Diagonal.AlignedChunks

end OAI
