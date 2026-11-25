import OAI.LinearAlgebra.SpectralBooks.Fermion.WickDeterminant
import Mathlib.Data.List.InsertIdx

/-! # Full contractions of the two tagged field blocks -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

/-- Independently relabeling the two words pulls the scalar kernel back
along the two relabelings. -/
theorem fullContractions_map {α β R : Type*} [CommRing R] (κ : β → β → R)
    (f g : α → β) (l r : List α) :
    fullContractions κ (l.map f) (r.map g) =
      fullContractions (fun x y ↦ κ (f x) (g y)) l r := by
  induction l generalizing r with
  | nil =>
    change (∑ _ : Unit, if (r.map g).isEmpty then (1 : R) else 0) =
      ∑ _ : Unit, if r.isEmpty then (1 : R) else 0
    simp
  | cons x l ih =>
    simp only [List.map_cons, fullContractions_cons]
    apply Fintype.sum_equiv (finCongr (List.length_map (f := g)))
    intro j
    simp only [List.length_map, List.getElem_map, List.eraseIdx_map, ih]
    rfl

/-- The field's Boolean tag selects its formal variable. The numerator of
a contracted pair depends only on the two derivative orders. -/
theorem fullContractions_tagged_kernelNumerator (I J : Finset ℕ) (h : J.card = I.card)
    (first second : Bool) :
    fullContractions (fun f g : Bool × ℕ ↦ kernelNumerator f.2 g.2)
      ((I.sort (· ≤ ·)).map (fun i ↦ (first, i)))
      ((J.sort (· ≤ ·)).map (fun j ↦ (second, j))) = pairing I J := by
  rw [fullContractions_map]
  exact fullContractions_kernelNumerator I J h

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
