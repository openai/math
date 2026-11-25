import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.Perm.Basic

/-! # Coordinate permutations of words of fixed content

The balanced words in the permutation stretch are the special case where every
letter has the same multiplicity. The coordinate permutation carrying one word
to another is assembled from bijections between their corresponding fibers.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- Words on the alphabet `α` with positions indexed by `ι` and prescribed
multiplicity for each letter. -/
def WordsOfContent (ι α : Type*) [Fintype ι] [DecidableEq α] (counts : α → ℕ) :=
  {w : ι → α // ∀ a, Fintype.card {i : ι // w i = a} = counts a}

namespace WordsOfContent

variable {ι α : Type*} [Fintype ι] [DecidableEq α] {counts : α → ℕ}

noncomputable instance [Fintype α] : Fintype (WordsOfContent ι α counts) := by
  classical
  unfold WordsOfContent
  infer_instance

/-- Move each coordinate of a word from position `i` to position `π i`. -/
def permute (π : Equiv.Perm ι) (w : WordsOfContent ι α counts) : WordsOfContent ι α counts :=
  ⟨w.1 ∘ π.symm, fun a ↦ (Fintype.card_congr
    (Equiv.subtypeEquivOfSubtype (p := fun i ↦ w.1 i = a) π.symm)).trans (w.2 a)⟩

instance : MulAction (Equiv.Perm ι) (WordsOfContent ι α counts) where
  smul := permute
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

@[simp] theorem smul_apply (π : Equiv.Perm ι) (w : WordsOfContent ι α counts) (i : ι) :
    (π • w).1 i = w.1 (π.symm i) := rfl

/-- A bijection of each pair of letter fibers gives a permutation of all positions. -/
instance : MulAction.IsPretransitive (Equiv.Perm ι) (WordsOfContent ι α counts) where
  exists_smul_eq v w := by
    let e (a : α) : {i : ι // w.1 i = a} ≃ {i : ι // v.1 i = a} :=
      Fintype.equivOfCardEq ((w.2 a).trans (v.2 a).symm)
    exact ⟨(Equiv.ofFiberEquiv e).symm,
      Subtype.ext (funext fun i ↦ Equiv.ofFiberEquiv_map e i)⟩

end WordsOfContent

end SpectralBooks
end LinearAlgebra
end OAI
