import OAI.Computability.BorderVNP.ResidueAmbientJet
import OAI.Computability.BorderVNP.ResidueJetJacobian

/-! # Polynomial and mixed Laurent evaluation in a shifted chart

Chart equations are ordinary polynomials in all coordinates. Test expressions
may also use negative powers of the time parameter. These embeddings and
substitutions identify the same evaluations in both representations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open ResidueBox MvPolynomial
open scoped Classical

variable {σ E B : Type*} [CommRing E] [CommRing B]

private def polynomialMixedIndex : ((Option σ) →₀ ℕ) →+ ((σ → ℕ) × ℤ) where
  toFun m := (fun i => m (some i), m none)
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp

/-- Embed chart polynomials in the algebra with signed exponents at time. -/
noncomputable def polynomialMixed : MvPolynomial (Option σ) E →+* Mixed σ E :=
  AddMonoidAlgebra.mapDomainRingHom E polynomialMixedIndex

/-- Embedding again in the full Laurent algebra agrees with the direct polynomial embedding. -/
theorem mixedToLaurent_polynomialMixed (g : MvPolynomial (Option σ) E) :
    mixedToLaurent (polynomialMixed g) = toLaurent g := by
  have h : mixedIndex.comp (polynomialMixedIndex (σ := σ)) = polynomialExponents (Option σ) := by
    ext m i
    cases i <;> rfl
  change (AddMonoidAlgebra.mapDomainRingHom E mixedIndex).comp
    (AddMonoidAlgebra.mapDomainRingHom E polynomialMixedIndex) g = _
  rw [← AddMonoidAlgebra.mapDomainRingHom_comp, h]
  rfl

variable [Fintype σ]

/-- Evaluation of embedded chart equations at their parameter and unit time values. -/
theorem mixedEval_polynomialMixed (φ : E →+* B) (x : σ → B) (t : Bˣ)
    (g : MvPolynomial (Option σ) E) :
    mixedEval φ x t (polynomialMixed g) = eval₂Hom φ (fun i => i.elim (t : B) x) g := by
  have h : (mixedEval φ x t).comp polynomialMixed = eval₂Hom φ (fun i => i.elim (t : B) x) := by
    apply ringHom_ext
    · intro c
      change mixedEval φ x t (AddMonoidAlgebra.mapDomain polynomialMixedIndex (.single 0 c)) = _
      rw [AddMonoidAlgebra.mapDomain_single, mixedEval_single]
      simp [polynomialMixedIndex]
    · intro j
      change mixedEval φ x t (AddMonoidAlgebra.mapDomain polynomialMixedIndex
        (.single (Finsupp.single j 1) 1)) = _
      rw [AddMonoidAlgebra.mapDomain_single, mixedEval_single]
      cases j with
      | none => simp [polynomialMixedIndex]
      | some j =>
        simp only [polynomialMixedIndex, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_mul,
          Finsupp.single_apply, eval₂Hom_X', Option.elim_some]
        simp [apply_ite]
  exact DFunLike.congr_fun h g

/-- Shift ordinary chart coordinates by nilpotent variables while keeping signed time powers
in the coefficient ring, via the unit C(t). -/
noncomputable def shiftMixed (φ : E →+* B) (x : σ → B) (t : Bˣ) :
    Mixed σ E →+* MvPolynomial σ B :=
  mixedEval (C.comp φ) (fun i => C (x i) + X i) (Units.map C.toMonoidHom t)

/-- Its image in the truncated ring is the mixed evaluation at the nilpotent coordinates. -/
theorem mk_shiftMixed (d : ℕ) (φ : E →+* B) (x : σ → B) (t : Bˣ) (f : Mixed σ E) :
    JetRing.mk d (shiftMixed φ x t f) =
      mixedEval ((algebraMap B (JetRing.Carrier σ B d)).comp φ)
        (fun i => algebraMap B _ (x i) + JetRing.coord d i)
        (Units.map (algebraMap B _).toMonoidHom t) f := by
  rw [shiftMixed, mixedEval_map]
  congr 2

/-- The constant term of a shifted Laurent test is its branch evaluation. -/
theorem shiftMixed_constant (φ : E →+* B) (x : σ → B) (t : Bˣ) (f : Mixed σ E) :
    constantCoeff (shiftMixed φ x t f) = mixedEval φ x t f := by
  rw [shiftMixed, mixedEval_map]
  congr 2
  · ext c
    simp
  · funext i
    simp
  · apply Units.ext
    simp

/-- On the chart equations the mixed shift is the polynomial shift used for the Jacobian. -/
theorem shiftMixed_polynomialMixed (φ : E →+* B) (x : σ → B) (t : Bˣ)
    (g : MvPolynomial (Option σ) E) :
    shiftMixed φ x t (polynomialMixed g) = JetRing.shiftChart φ (fun i => i.elim (t : B) x) g := by
  rw [shiftMixed, mixedEval_polynomialMixed]
  unfold JetRing.shiftChart
  congr 2
  funext i
  cases i <;> rfl

end Residue

end BorderVNP
end Computability
end OAI
