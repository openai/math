import OAI.LinearAlgebra.SpectralBooks.WordPermutations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-! # Selector cables of a fixed-profile contraction

The center chooses a word with the specified multiplicities. Every endpoint gets one copy of its
binary encoding. Invalid words and inconsistent copies contribute zero.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Crossing

open scoped BigOperators Classical

noncomputable section

variable {W S V F : Type*} [Fintype W] [Fintype S] [Fintype V] [CommSemiring F]

/-- An endpoint reads one selector cable and rejects invalid codes. -/
def readSelector (code : W ↪ S) (g : W → F) (c : S) : F :=
  if h : ∃ w, code w = c then g h.choose else 0

omit [Fintype S] in
@[simp] theorem readSelector_code (code : W ↪ S) (g : W → F) (w : W) :
    readSelector code g (code w) = g w := by
  simp [readSelector]

/-- Sum over independently assigned selector cables. The center enforces a common code. -/
def selectorBroadcast (code : W ↪ S) (g : Option V → W → F) : F :=
  ∑ cable : V → S,
    (∑ w, if cable = fun _ ↦ code w then g none w else 0) *
      ∏ v, readSelector code (g (some v)) (cable v)

theorem selectorBroadcast_eq (code : W ↪ S) (g : Option V → W → F) :
    selectorBroadcast code g = ∑ w, ∏ i, g i w := by
  unfold selectorBroadcast
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Fintype.prod_option]

/-- Coordinates of the selector cable. Order is the order of the external slots. -/
def profileCode {A : Type*} [DecidableEq A] {π : A → ℕ} {b j : ℕ} (code : A ↪ (Fin b → Bool)) :
    WordsOfContent (Fin j) A π ↪ (Fin j → Fin b → Bool) where
  toFun w i := code (w.1 i)
  inj' := fun _ _ h ↦ Subtype.ext (funext fun i ↦ code.injective (congrFun h i))

end

end Crossing

end SpectralBooks
end LinearAlgebra
end OAI
