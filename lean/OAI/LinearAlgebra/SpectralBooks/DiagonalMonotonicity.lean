import OAI.LinearAlgebra.SpectralBooks.PlacementDiagonal
import OAI.LinearAlgebra.SpectralBooks.MaskDiagonalPrice
import OAI.LinearAlgebra.SpectralBooks.RawLogPrice
import OAI.LinearAlgebra.SpectralBooks.SpectralDiagonal

/-! # Monotonicity under adjoining sites

To forget some recipients of a common label, locally forget the corresponding
basis indices. The restriction inequality at a point on the larger site set then
compares the two diagonal prices.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open scoped Classical

section

open SiteTensor

namespace SpectralPlacementPrices

variable {K : Type*} {X : Type} [Field K] [MetricSpace X] (P : SpectralPlacementPrices K X)

/-- The price of a binary diagonal is monotone in its finite set of recipients. -/
theorem diagonal_mono : Monotone P.diagonal := by
  intro S T hST
  by_cases he : S = ∅
  · subst S
    rw [P.diagonal_empty]
    exact P.diagonal_nonneg T
  have hS := Finset.nonempty_iff_ne_empty.mpr he
  have hT := hS.mono hST
  cases subsingleton_or_nontrivial T with
  | inl hs =>
    obtain ⟨s, hsS⟩ := hS
    have hTS : T ⊆ S := fun t ht ↦ by
      have hts : t = s := congrArg Subtype.val (Subsingleton.elim (⟨t, ht⟩ : T) ⟨s,hST hsS⟩)
      exact hts.symm ▸ hsS
    rw [Finset.Subset.antisymm hST hTS]
  | inr hnt =>
    let e : T ↪ X := Function.Embedding.subtype _
    let U : Finset T := Finset.univ.filter (fun i ↦ i.val ∈ S)
    have hU : U.Nonempty := by
      obtain ⟨x,hx⟩ := hS
      exact ⟨⟨x,hST hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩
    have hUS : U.map e = S := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
        exact (Finset.mem_filter.mp hi).2
      · exact fun hx ↦ Finset.mem_map.mpr ⟨⟨x,hST hx⟩, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,hx⟩, rfl⟩
    have hUT : (Finset.univ : Finset T).map e = T := by ext; simp [e]
    obtain ⟨φ, c, hc, hm⟩ := P.exists_point_diagonal_map e
    have hle := rawLogPrice_mono φ hc
      (Raw.maskDiagonal_restricts_of_subset (K := K) (Finset.subset_univ U) (Fin 2))
    change c * Real.logb 2 _ ≤ c * Real.logb 2 _ at hle
    rw [← hm U hU, ← hm Finset.univ Finset.univ_nonempty, hUS, hUT] at hle
    exact hle

end SpectralPlacementPrices

end

end

end SpectralBooks
end LinearAlgebra
end OAI
