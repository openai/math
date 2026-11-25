import OAI.Computability.BorderVNP.ResidueAmbientJet
import OAI.Computability.BorderVNP.ResiduePinsBasis

/-!
# Branch evaluation of the finite test space

The coordinate functions may vanish on the branch. Only the parameter has an inverse.
Restriction from the full Laurent exponent array to the mixed chart therefore discards
terms with a negative polynomial-coordinate exponent. Every Laurent array used in the
pins lies in the chart, where evaluation is multiplicative.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResiduePins

open Residue ResidueBox
open scoped BigOperators Classical

variable {σ E A : Type*} [CommSemiring E]

/-- The Laurent coefficient array is polynomial in all the non-parameter coordinates. -/
def chartSupported (f : Laurent σ E) : Prop := ∀ d ∈ f.coeff.support, ∀ i, 0 ≤ d (some i)

private theorem mixedIndex_injective : Function.Injective (mixedIndex (σ := σ)) := by
  intro e d h
  apply Prod.ext
  · funext i
    exact Int.ofNat_inj.mp (congrFun h (some i))
  · exact congrFun h none

/-- Retain exactly the coefficients indexed by the mixed chart monomials. -/
noncomputable def restrictChart : Laurent σ E →+ Mixed σ E :=
  AddMonoidAlgebra.comapDomainAddMonoidHom mixedIndex mixedIndex_injective

/-- Restriction is a left inverse to the embedding of the mixed chart. -/
theorem restrictChart_embed (f : Mixed σ E) : restrictChart (mixedToLaurent f) = f := by
  apply AddMonoidAlgebra.coeff_injective
  exact Finsupp.comapDomain_mapDomain mixedIndex mixedIndex_injective f.coeff

/-- Reembedding a chart-supported coefficient array recovers all of it. -/
theorem embed_restrictChart (f : Laurent σ E) (hf : chartSupported f) :
    mixedToLaurent (restrictChart f) = f := by
  apply AddMonoidAlgebra.mapDomain_comapDomain (hf := mixedIndex_injective)
  intro d hd
  refine ⟨(fun i => (d (some i)).toNat, d none), ?_⟩
  funext i
  cases i with
  | none => rfl
  | some i => exact Int.toNat_of_nonneg (hf d hd i)

/-- A single monomial with nonnegative polynomial coordinates belongs to the chart. -/
theorem chartSupported_single (d : Exponent σ) (a : E) (hd : ∀ i, 0 ≤ d (some i)) :
    chartSupported (AddMonoidAlgebra.single d a) := by
  intro e he
  have : e = d := Finset.mem_singleton.mp (Finsupp.support_single_subset he)
  rwa [this]

/-- The embedded chart has no negative exponents in its polynomial coordinates. -/
theorem chartSupported_embed (f : Mixed σ E) : chartSupported (mixedToLaurent f) := by
  intro d hd
  change d ∈ (f.coeff.mapDomain mixedIndex).support at hd
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hd)
  exact fun i => Int.natCast_nonneg (e.1 i)

variable [Fintype σ]

/-- The additive extension of mixed-chart evaluation to signed exponent arrays. -/
noncomputable def evaluate {F : Type*} [CommRing F] [CommRing A]
    (φ : F →+* A) (x : σ → A) (t : Aˣ) : Laurent σ F →+ A :=
  (mixedEval φ x t).toAddMonoidHom.comp restrictChart

/-- Evaluation of an embedded chart polynomial is its ordinary mixed evaluation. -/
theorem evaluate_embed {F : Type*} [CommRing F] [CommRing A] (φ : F →+* A)
    (x : σ → A) (t : Aˣ) (f : Mixed σ F) :
    evaluate φ x t (mixedToLaurent f) = mixedEval φ x t f := by
  change mixedEval φ x t (restrictChart (mixedToLaurent f)) = _
  rw [restrictChart_embed]

/-- The monomial value of the basis test, allowing a negative time exponent. -/
theorem evaluate_test {k F β : Type*} [Field k] [Field F] [Algebra k F] [CommRing A]
    (φ : F →+* A) (x : σ → A) (t : Aˣ) (B : Module.Basis β k F)
    {H : ℕ} (i : Index β σ H) :
    evaluate φ x t (test B i) = φ (B i.1) *
      ((↑(t ^ i.2.val none) : A) * ∏ s, x s ^ (i.2.val (some s)).toNat) := by
  let d : (σ → ℕ) × ℤ := (fun s => (i.2.val (some s)).toNat, i.2.val none)
  have hd : mixedIndex d = i.2.val := by
    funext j
    cases j with
    | none => rfl
    | some s => exact Int.toNat_of_nonneg (i.2.property.2 s).1
  change evaluate φ x t (AddMonoidAlgebra.single i.2.val (B i.1)) = _
  rw [← hd, ← mixedToLaurent_single, evaluate_embed, mixedEval_single]
  rfl

/-- The extended evaluation is multiplicative on the actual chart. -/
theorem evaluate_mul {F : Type*} [CommRing F] [CommRing A] (φ : F →+* A)
    (x : σ → A) (t : Aˣ) (f g : Laurent σ F) (hf : chartSupported f) (hg : chartSupported g) :
    evaluate φ x t (f * g) = evaluate φ x t f * evaluate φ x t g := by
  conv_lhs => rw [← embed_restrictChart f hf, ← embed_restrictChart g hg, ← map_mul]
  rw [evaluate_embed, map_mul]
  rfl

omit [Fintype σ] in
/-- The output of the box test extraction has nonnegative polynomial coordinates. -/
theorem chartSupported_extracted_test {ι F : Type*} [Fintype ι] [CommSemiring F]
    (L q : ℕ) (hq : 2 ≤ q) (g : ι → MvPolynomial (Option σ) F) (root : F →+* F)
    (b : F) (e : Exponent σ) (he : InBox (radius L (∑ i, (g i).totalDegree)) e) :
    chartSupported (extract q (by omega) root (AddMonoidAlgebra.single e b * equationProduct q g)) := by
  intro d hd i
  have hrow : d ∈ (rowPolynomial q (by omega) g root 1 b e 0).coeff.support := by
    change d ∈ ((1 : Laurent σ F) * extract q (by omega) root
      (AddMonoidAlgebra.single e b * equationProduct q g)).coeff.support
    simpa only [one_mul] using hd
  exact ((row_supported hq g root 1 b e 0 he rfl (fun _ => ⟨le_rfl, Int.natCast_nonneg _⟩)
    hrow).2 i).1

end ResiduePins

end BorderVNP
end Computability
end OAI
