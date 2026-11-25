import OAI.Computability.BorderVNP.DiagonalStretchAssembly
import OAI.Computability.BorderVNP.CrossingNormalization
import OAI.Computability.BorderVNP.ModelGroundImage
import OAI.Computability.BorderVNP.RateCrossing

/-! # The profile-shortening hypothesis and the degree-component size in Theorem 3.2 -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Rate

open Crossing Diagonal Filter MvPolynomial

/-- Normalizing a shortening can increase its terminal multiplicity. Quantifying
over multiplicities gives exactly the paper's existential shortening hypothesis.
The closure over the algebraically closed ground field gives the same minimum
gate count as the geometric closure used by the residue construction. -/
theorem primeFieldStretch_iff_profile (K : Type) [Field K] :
    PrimeFieldStretch K ↔
      (HasProfileShortening (AlgebraicClosure K) →
        ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, (2 : ℝ)^((n : ℝ)^ε) ≤
          groundBorderSize n (map (Int.castRingHom (AlgebraicClosure K)) (Pstar n))) := by
  simp only [← borderSize_eq_groundBorderSize]
  constructor
  · intro stretch small
    obtain ⟨D,hD,m,hm,identity⟩ := (hasProfileShortening_iff_paid _).mp small
    exact stretch D hD m hm identity
  · intro stretch D hD m hm identity
    exact stretch ((hasProfileShortening_iff_paid _).mpr ⟨D,hD,m,hm,identity⟩)

/-- An installed native column for each paid identity supplies the stretch
lemma with the exponent of the schedule selected for that identity. -/
theorem primeFieldStretch_of_native_columns (K : Type) [Field K] (q : ℕ) [CharP K q]
    (construct : ∀ D ≥ 2, ∀ m > 0, ∀ G : PaidIdentity (AlgebraicClosure K) D m,
      ∃ (ι : Type) (enumeration : Fintype ι) (aux : ι → AlgebraicClosure K) (S : StretchSchedule),
        @NativeColumns (AlgebraicClosure K) _ D m ι enumeration q G aux S) : PrimeFieldStretch K := by
  rintro D hD m hm ⟨G⟩
  obtain ⟨ι,enumeration,aux,S,run⟩ := construct D hD m hm G
  let : Fintype ι := enumeration
  exact ⟨S.σ,S.positive,stretch_of_native_columns q G aux S run (AlgebraicClosure K)⟩

end Rate

end BorderVNP
end Computability
end OAI
