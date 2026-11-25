import OAI.LinearAlgebra.SpectralBooks.BookCollapseLeft
import OAI.LinearAlgebra.SpectralBooks.BookCollapseRight
import OAI.LinearAlgebra.SpectralBooks.BookGroupSupport
import OAI.LinearAlgebra.SpectralBooks.SitePriceEval.GroupedPriceLaws
import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport
import OAI.LinearAlgebra.SpectralBooks.StretchClassPrice

/-!
# Zero wire distances imply the two collapsed placement laws

The ambient site set contains the book and an arbitrary finite set of auxiliary
sites. The binary wires and all logarithmic prices are evaluated at that full
site set. Moving private legs uses the tensor transport inequalities and leaves
a scalar slot at every auxiliary site.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section

open Foundation SiteTensor
open scoped Classical

variable {K : Type*} [Field K] {B C O : Type} [Fintype B] [Fintype C] [Fintype O]

/-- Every wire from the common site to a site of the right-hand family has zero price. -/
def WireCollapseC (g : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ) : Prop :=
  ∀ c : C, classPrice g (ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group
    ![.inl (.inl ()), .inl (.inr (.inr c))])) = 0

/-- Every wire from the common site to a site of the left-hand family has zero price. -/
def WireCollapseB (g : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ) : Prop :=
  ∀ b : B, classPrice g (ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group
    ![.inl (.inl ()), .inl (.inr (.inl b))])) = 0

/-- The zero-distance transport inequality on supported tensors, stated on
the original price of nonzero tensor classes. -/
private theorem supported_group_price {S : Type} [Fintype S] [Nonempty S]
    (g : NonzeroProduct.{0} (S ⊕ O) K →+ ℝ) (hg : IsSpectralPrice unit_le_nonzeroClass g)
    (T : Raw.{0} S K) (σ : S → S)
    (hwire : ∀ i, σ i ≠ i → classPrice g (ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group
      ![.inl (σ i), .inl i])) = 0) :
    classPrice g (ofRaw (Raw.withTrivial O (T.group σ))) =
      classPrice g (ofRaw (Raw.withTrivial O T)) := by
  rcases hg with rfl | ⟨φ, c, hc, rfl⟩
  · simp
  · rw [← ofRaw_eq_iff.mpr (T.group_support_equivalent σ O),
      ← ofRaw_eq_iff.mpr (T.group_inl_equivalent O)]
    simp only [classPrice_scaled_log]
    apply rawLogPrice_eq_of_collapsed φ c hc.le T (fun i => Sum.inl (σ i)) Sum.inl
    intro i
    by_cases hi : σ i = i
    · rw [hi]
      exact rawWireDistance_self φ c hc.le _
    · simpa only [rawWireDistance, rawLogPrice, classPrice_scaled_log] using hwire i hi

private theorem supported_eq_of_equivalent {S : Type} [Fintype S] [Nonempty S]
    (g : NonzeroProduct.{0} (S ⊕ O) K →+ ℝ) {T U : Raw.{0} S K} (h : T.Equivalent U) :
    classPrice g (ofRaw (Raw.withTrivial O T)) = classPrice g (ofRaw (Raw.withTrivial O U)) :=
  congrArg (classPrice g) (congrArg (withTrivialHom O) (ofRaw_eq_iff.mpr h))

variable (g : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ)
  (hg : IsSpectralPrice unit_le_nonzeroClass g)

/-- Zero binary-wire price to each right-hand site allows arbitrary linear operations
after grouping the entire right-hand family at the center. -/
theorem wireCollapseC_monoGroupedC (h : WireCollapseC g) :
    (SitePriceEval.ofSupportedClassPrice g hg).MonoGroupedC := by
  apply (SitePriceEval.monoGroupedC_iff_groupingInvariant _).2
  intro U X Y _ _ _ T
  change classPrice g (ofRaw (Raw.withTrivial O (bookRaw (groupRight T)))) = _
  rw [← supported_eq_of_equivalent g (bookRaw_group_collapseRight T)]
  apply supported_group_price g hg
  rintro (u | (b | c)) hi
  · cases u
    exact (hi rfl).elim
  · exact (hi rfl).elim
  · exact h c

/-- Zero binary-wire price to each left-hand site gives the symmetric grouped law. -/
theorem wireCollapseB_monoGroupedB (h : WireCollapseB g) :
    (SitePriceEval.ofSupportedClassPrice g hg).MonoGroupedB := by
  apply (SitePriceEval.monoGroupedB_iff_groupingInvariant _).2
  intro U X Y _ _ _ T
  change classPrice g (ofRaw (Raw.withTrivial O (bookRaw (groupLeft T)))) = _
  rw [← supported_eq_of_equivalent g (bookRaw_group_collapseLeft T)]
  apply supported_group_price g hg
  rintro (u | (b | c)) hi
  · cases u
    exact (hi rfl).elim
  · exact h b
  · exact (hi rfl).elim

end

end

end SpectralBooks
end LinearAlgebra
end OAI
