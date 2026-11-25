import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
namespace ThreeFlat.FoldInput

abbrev Port (L copies p B : ℕ) := ((Fin L × Fin copies) × Fin p) ⊕ (Bool × Fin B)

def flagIndex : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i = 1)
  left_inv b := by cases b <;> decide
  right_inv i := by
    rcases i with ⟨i,hi⟩
    have h : i = 0 ∨ i = 1 := by omega
    rcases h with rfl | rfl <;> rfl

def rowMajor {L copies p B : ℕ} : Port L copies p B ≃ Fin (L*copies*p + 2*B) :=
  (Equiv.sumCongr ((finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv)
    ((flagIndex.prodCongr (Equiv.refl _)).trans finProdFinEquiv)).trans finSumFinEquiv

def pins {L copies p B : ℕ} (input : Port L copies p B → Bool)
    (t : Fin L) (i : Fin copies) (j : Fin p) := input (.inl ((t,i),j))

def boundary {L copies p B : ℕ} (input : Port L copies p B → Bool)
    (flag : Bool) (j : Fin B) := input (.inr (flag,j))

end ThreeFlat.FoldInput

end OAI
