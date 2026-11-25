import OAI.Computability.BorderVNP.ResidueApproximationPlace
import OAI.Computability.BorderVNP.ResidueAmbientJet

/-! # The nonzero test in the mixed chart algebra

Combine the two nonnegative time exponents of a polynomial in `x,t,t⁻¹` into
a single signed exponent. This expresses the residue-one test in the chart
algebra on which the ambient Cartier coefficient extractor acts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open MvPolynomial HahnSeries IsLocalRing

variable {ι E B : Type*} [Field E] [Field B]

/-- The two time-variable exponents enter the actual Laurent exponent with opposite signs. -/
def signedTimeExponent : ((ι ⊕ Bool) →₀ ℕ) →+ ((ι → ℕ) × ℤ) where
  toFun m := (fun i => m (.inl i), (m (.inr true) : ℤ) - m (.inr false))
  map_zero' := by simp; rfl
  map_add' m n := by ext i <;> simp; ring

/-- Send the two time indeterminates to the same parameter and its inverse. -/
noncomputable def toMixedTest : MvPolynomial (ι ⊕ Bool) E →+* Mixed ι E :=
  AddMonoidAlgebra.mapDomainRingHom E signedTimeExponent

/-- Evaluation after identifying the two time variables agrees with ordinary
polynomial evaluation at the selected tuple. -/
theorem eval_toMixedTest [Fintype ι] (φ : E →+* B) (x : ι → B) (t : Bˣ)
    (f : MvPolynomial (ι ⊕ Bool) E) : mixedEval φ x t (toMixedTest f) =
      eval₂ φ (Sum.elim x (fun b => if b then (t : B) else (t : B)⁻¹)) f := by
  classical
  have h : (mixedEval φ x t).comp toMixedTest =
      eval₂Hom φ (Sum.elim x (fun b => if b then (t : B) else (t : B)⁻¹)) := by
    apply ringHom_ext
    · intro c
      change mixedEval φ x t (AddMonoidAlgebra.mapDomain signedTimeExponent (.single 0 c)) = _
      rw [AddMonoidAlgebra.mapDomain_single, mixedEval_single]
      simp [signedTimeExponent]
    · intro j
      change mixedEval φ x t (AddMonoidAlgebra.mapDomain signedTimeExponent
        (.single (Finsupp.single j 1) 1)) = _
      rw [AddMonoidAlgebra.mapDomain_single, mixedEval_single]
      rcases j with (i | b)
      · simp [signedTimeExponent, Finsupp.single_apply, apply_ite]
      · cases b <;> simp [signedTimeExponent]
  exact DFunLike.congr_fun h f

variable {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (p : ℕ) [Fact p.Prime] [CharP O p] [CharP (ResidueField O) p] [Finite (ResidueField O)]
  (π : O) (hπ : Irreducible π) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra E K]

attribute [local instance] branchPrimeAlgebra

/-- Section 10.2's actual mixed Laurent test, before the high Cartier power
compresses its support to the prescribed box. -/
theorem exists_trace_one_mixed [Fintype ι] (x : ι → K) (t : Kˣ)
    (hgen : IntermediateField.adjoin E (insert (t : K) (Set.range x)) = ⊤)
    (ht : 0 < (branchLaurentExpansion p π hπ K (t : K)).order)
    (η : LaurentSeries (ResidueField O)) (hη : η ≠ 0) :
    let ρ := branchLaurentExpansion p π hπ K
    ∃ f : Mixed ι E, tracedRes p (mixedEval (ρ.comp (algebraMap E K))
      (ρ ∘ x) (Units.map ρ.toMonoidHom t) f * η) = 1 := by
  obtain ⟨f, hf⟩ := exists_trace_one_polynomial p π hπ x (t : K) hgen ht η hη
  exact ⟨toMixedTest f, by rw [eval_toMixedTest]; exact hf⟩

end Residue

end BorderVNP
end Computability
end OAI
