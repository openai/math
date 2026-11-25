import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetCyclotomic

/-! # Power-basis coordinates of a quadratic jet block

The decoder orders the quadratic, jet, and coefficient indices differently from the
encoder. Both orders represent the same power basis in the iterated monic quotient.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped Classical

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] {e h : ℕ}

/-- The rectangular monomial expansion consists of the power-basis expansions of its rows. -/
theorem jetBivariate_eq_ofFn (a : JetArray S e h) :
    jetBivariate a = ofFn h (fun t => ofFn e (fun i => a (t,i))) := by
  simp only [jetBivariate, ofFn_eq_sum_monomial, Fintype.sum_prod_type, map_sum]

/-- Reindexing the coordinates of a decoded block gives its ordinary jet array. -/
theorem jetOutputValueOver_eq_jetQuotientValue (φ : R →+* S) (η : S) (m : S[X])
    (y : (Fin 2 × Fin h) × Fin e → R) :
    jetOutputValueOver φ η m y = jetQuotientValue m (quadraticJetArray φ η
      (fun i => y ((0,i.1),i.2)) (fun i => y ((1,i.1),i.2))) := by
  rw [jetQuotientValue, jetBivariate_eq_ofFn]
  rfl

/-- Evaluating the first `deg m` powers of the root gives exactly the monic power basis. -/
theorem mk_ofFn_bijective {m : S[X]} (hm : m.Monic) (hd : m.natDegree = e) :
    Function.Bijective (fun c : Fin e → S => AdjoinRoot.mk m (ofFn e c)) := by
  subst e
  have H := (AdjoinRoot.powerBasisAux' hm).equivFun.symm.bijective
  unfold AdjoinRoot.powerBasisAux' at H
  rw [Module.Basis.equivFun_ofEquivFun] at H
  convert H using 1
  funext c
  rw [ofFn_eq_sum_monomial]
  rfl

/-- The scalar coordinates in a quadratic monic quotient are precisely the coefficients of
`1` and the root. This applies to both quadratic cyclotomic orders. -/
theorem quadratic_root_coordinates_bijective {m : R[X]} (hm : m.Monic) (hd : m.natDegree = 2) :
    Function.Bijective (fun u : Fin 2 → R =>
      algebraMap R (AdjoinRoot m) (u 0) + AdjoinRoot.root m * algebraMap R _ (u 1)) := by
  have H := mk_ofFn_bijective hm hd
  convert H using 1
  funext u
  rw [ofFn_eq_sum_monomial, Fin.sum_univ_two]
  change _ = AdjoinRoot.mk m (monomial 0 (u 0) + monomial 1 (u 1))
  rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, pow_zero, mul_one, pow_one,
    map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.mk_C, mul_comm]
  rfl

private theorem jetQuotientValue_eq_nested (m : S[X]) (a : JetArray S e h) :
    jetQuotientValue m a = AdjoinRoot.mk (X ^ h)
      (ofFn h (fun t => AdjoinRoot.mk m (ofFn e fun i => a (t,i)))) := by
  simp only [jetQuotientValue, jetBivariate_eq_ofFn, ofFn_eq_sum_monomial, Polynomial.map_sum,
    map_monomial]

/-- A jet over a positive-degree monic modulus has a unique rectangular coefficient array. -/
theorem jetQuotientValue_bijective {m : S[X]} (hm : m.Monic) (hd : m.natDegree = e)
    (he : 0 < e) : Function.Bijective (jetQuotientValue (e := e) (h := h) m) := by
  have : Nontrivial S := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · have : m = 0 := Subsingleton.elim _ _
      simp [this] at hd
      omega
    · exact hs
  have : Nontrivial (AdjoinRoot m) := (AdjoinRoot.nontrivial_iff_of_monic hm).mpr (by
    rw [degree_eq_natDegree hm.ne_zero, hd]
    exact_mod_cast he)
  have outer := mk_ofFn_bijective (monic_X_pow h : ((X : (AdjoinRoot m)[X]) ^ h).Monic)
    (natDegree_X_pow h)
  have inner := mk_ofFn_bijective hm hd
  change Function.Bijective (fun a : JetArray S e h => jetQuotientValue m a)
  simp only [jetQuotientValue_eq_nested]
  constructor
  · intro a b hab
    have H := outer.injective hab
    funext ⟨t,i⟩
    exact congrFun (inner.injective (congrFun H t)) i
  · intro z
    obtain ⟨c,hc⟩ := outer.surjective z
    choose d hd using fun t => inner.surjective (c t)
    exact ⟨fun i => d i.1 i.2, by simpa only [hd] using hc⟩

/-- Equality of block values determines every base-ring output coordinate, and every jet
element admits those coordinates. -/
theorem jetOutputValueOver_bijective (φ : R →+* S) (η : S)
    (basis : Function.Bijective (fun u : Fin 2 → R => φ (u 0) + η * φ (u 1)))
    {m : S[X]} (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e) :
    Function.Bijective (jetOutputValueOver (e := e) (h := h) φ η m) := by
  have jets := jetQuotientValue_bijective (h := h) hm hd he
  constructor
  · intro a b hab
    simp only [jetOutputValueOver_eq_jetQuotientValue] at hab
    have H := jets.injective hab
    funext ⟨⟨q,t⟩,i⟩
    exact congrFun (basis.injective (a₁ := fun j => a ((j,t),i))
      (a₂ := fun j => b ((j,t),i)) (congrFun H (t,i))) q
  · intro z
    obtain ⟨a,ha⟩ := jets.surjective z
    choose c hc using fun i => basis.surjective (a i)
    refine ⟨fun i => c (i.1.2,i.2) i.1.1, ?_⟩
    rw [jetOutputValueOver_eq_jetQuotientValue, ← ha]
    exact congrArg (jetQuotientValue m) (funext hc)

/-- The base-defined modulus decoder agrees with the decoder for a modulus over the
quadratic order after coefficient extension. -/
theorem jetOutputValue_eq_over (φ : R →+* S) (η : S) (m : R[X])
    (y : (Fin 2 × Fin h) × Fin e → R) :
    jetOutputValue φ η m y = jetOutputValueOver φ η (m.map φ) y := by
  unfold jetOutputValue jetOutputValueOver
  congr 2
  congr 1
  funext t
  ext k
  rw [quadraticPolynomial_coeff]
  by_cases hk : k < e
  · simp only [ofFn_coeff_eq_val_of_lt _ hk]
  · simp only [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk), map_zero, mul_zero, add_zero]

/-- Base-defined cyclotomic blocks satisfy the uniform block-circuit interface. -/
theorem CyclotomicJetCircuits.toOver {k M h : ℕ} (H : CyclotomicJetCircuits R k M h) :
    let φ := algebraMap R (AdjoinRoot (cyclotomic k R))
    JetCircuitsOver φ (AdjoinRoot.root (cyclotomic k R)) ((cyclotomic M R).map φ) M.totient h := by
  obtain ⟨u,v,enc,dec,hu,hv,Hprod⟩ := H
  refine ⟨u,v,enc,dec,hu,?_,?_⟩
  · apply hv.trans
    apply Nat.add_le_add_left
    rw [Nat.mul_assoc, Nat.mul_left_comm]
    exact Nat.mul_le_mul_left h (by omega)
  · intro x y
    simpa only [jetOutputValue_eq_over] using Hprod x y

end

end FiniteFourier
end LinearAlgebra
end OAI
