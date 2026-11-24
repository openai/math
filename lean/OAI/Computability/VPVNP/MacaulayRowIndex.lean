import OAI.Computability.VPVNP.GradedMonomialIndex
import OAI.Computability.VPVNP.MacaulayCoordinates

/-!
# Entrywise queries in the finite-slice coefficient matrix

The indexed matrix of Appendix D is given by a scalar equation-coefficient
routine. A Macaulay entry needs at most one call to it. The appended rows and
targets are powered monomials, so their entries require only exponent tests.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex

open RankQuery MvPolynomial

variable {t d e L D N : ℕ} {K : Type*}

/-- Dense address of an equation and a multiplier monomial. -/
def rowEquiv (t e L : ℕ) : Fin (e * size t L) ≃ Fin e × BoundedMonomial t L :=
  finProdFinEquiv.symm.trans ((Equiv.refl _).prodCongr (enumeration t L))

/-- Coefficient of a monomial multiple of an equation, read at a dense column index. -/
def equationEntry [Zero K] (getCoeff : Fin e → (Fin t → ℕ) → K)
    (r : Fin (e * size t L)) (c : Fin (size t D)) : K :=
  let pair : Fin e × Fin (size t L) := finProdFinEquiv.symm r
  let a := indexedDigits pair.2
  let b := indexedDigits c
  if ∀ i, a i ≤ b i then getCoeff pair.1 (fun i => b i - a i) else 0

theorem equationEntry_eq [CommSemiring K] (F : Fin e → MvPolynomial (Fin t) K)
    (getCoeff : Fin e → (Fin t → ℕ) → K)
    (hget : ∀ i a, getCoeff i a = (F i).coeff (exponentVector a))
    (r : Fin (e * size t L)) (c : Fin (size t D)) :
    equationEntry getCoeff r c = macaulayMatrix F L D (rowEquiv t e L r) (enumeration t D c) := by
  rw [macaulayMatrix_apply]
  let pair : Fin e × Fin (size t L) := finProdFinEquiv.symm r
  change (if ∀ i, indexedDigits pair.2 i ≤ indexedDigits c i then _ else 0) =
    (if (enumeration t L pair.2).val ≤ (enumeration t D c).val then _ else 0)
  simp only [indexedDigits_eq, Finsupp.le_def, hget]
  split_ifs
  · apply congrArg ((F pair.1).coeff)
    exact Finsupp.ext fun _ => rfl
  · rfl

/-- An entry of a powered monomial row, computed without forming a polynomial. -/
def powerEntry [Zero K] [One K] (P : ℕ) (a : Fin t → ℕ) (c : Fin (size t D)) : K :=
  let b := indexedDigits c
  if ∀ i, P * a i = b i then 1 else 0

/-- A coefficient lookup agrees with taking the indicated power in the formal
polynomial ring. This identity also covers power zero and the empty tuple. -/
theorem powerEntry_eq [CommSemiring K] (P : ℕ) (a : Fin t → ℕ) (c : Fin (size t D)) :
    powerEntry P a c = coefficientRow D ((monomial (exponentVector a) (1 : K)) ^ P)
      (enumeration t D c) := by
  change _ = ((monomial (exponentVector a) (1 : K)) ^ P).coeff _
  rw [monomial_pow, one_pow, coeff_monomial]
  have he : (∀ i, P * a i = indexedDigits c i) ↔
      P • exponentVector a = (enumeration t D c).val := by
    rw [DFunLike.ext_iff]
    simp [exponentVector, indexedDigits_eq]
  simp only [powerEntry, he]

/-- The original (unpowered) monomial represented by a dense ordinal. -/
noncomputable def monomialAt [CommSemiring K] (t N : ℕ) (i : Fin (size t N)) :
    MvPolynomial (Fin t) K :=
  monomial (enumeration t N i).val 1

theorem powerEntry_indexed_eq [CommSemiring K] (P : ℕ) (j : Fin (size t N))
    (c : Fin (size t D)) :
    powerEntry P (indexedDigits j) c = coefficientRow D ((monomialAt t N j : MvPolynomial _ K) ^ P)
      (enumeration t D c) := by
  rw [powerEntry_eq]
  have he : exponentVector (indexedDigits j) = (enumeration t N j).val :=
    Finsupp.ext (indexedDigits_eq j)
  rw [he]; rfl

/-- A coordinate in the list of original monomial ordinals. Non-basis
ordinals return zero. All matrix arguments are entry routines. -/
def entryCoordinate [Field K] [DecidableEq K] (L D N P : ℕ)
    (getCoeff : Fin e → (Fin t → ℕ) → K) (target : Fin t → ℕ) : Fin (size t N) → K :=
  quotientCoordinate (m := size t D) (equationEntry (L := L) getCoeff)
    (fun j => powerEntry P (indexedDigits j)) (powerEntry P target)

theorem entryCoordinate_eq [Field K] [DecidableEq K] (L D N P : ℕ)
    (F : Fin e → MvPolynomial (Fin t) K) (getCoeff : Fin e → (Fin t → ℕ) → K)
    (hget : ∀ i a, getCoeff i a = (F i).coeff (exponentVector a)) (target : Fin t → ℕ) :
    entryCoordinate L D N P getCoeff target =
      macaulayCoordinateQuery F (monomialAt t N) (monomial (exponentVector target) 1) P
        (rowEquiv t e L) (enumeration t D) := by
  have heq : equationEntry (D := D) (L := L) getCoeff =
      (macaulayMatrix F L D).submatrix (rowEquiv t e L) (enumeration t D) :=
    funext fun r => funext fun c => equationEntry_eq F getCoeff hget r c
  unfold entryCoordinate macaulayCoordinateQuery indexedQuotientCoordinate
  rw [heq]
  congr 1
  · funext r c; exact powerEntry_indexed_eq P r c
  · funext c; exact powerEntry_eq P target c

end RadicalCertificate.MonomialIndex

end VPVNP
end Computability
end OAI
