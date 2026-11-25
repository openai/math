import OAI.LinearAlgebra.FiniteFourier.PrimeSpectrumEquiv
import OAI.LinearAlgebra.FiniteFourier.PrimeQueryProduct

/-! # Ordinary matrices of diagonal Fourier multipliers on paired tuples

Conjugating a pointwise multiplier by the positive-sign Fourier transform
gives its normalized inversion sum. Query powers and the full dot-product
query use the same conjugating equivalence.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open scoped Classical

variable {K ι : Type*} [CommRing K] [Fintype ι] {ℓ : ℕ} [NeZero ℓ] [Invertible (ℓ : K)] {ζ : K}

/-- Apply the frequency-dependent scalar `f` in the Fourier coordinates of a pair of tuples. -/
def primeSpectrumMultiplier (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (f : PrimeSpectrumDigits ι ℓ → K) :
    Module.End K (PrimeSpectrumDigits ι ℓ → K) :=
  let S := primeSpectrumEquiv (ι := ι) hζ
  S.symm.toLinearMap.comp ((LinearMap.mulLeft K f).comp S.toLinearMap)

theorem primeSpectrumMultiplier_apply (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (f v : PrimeSpectrumDigits ι ℓ → K) :
    primeSpectrumMultiplier hζ f v = (primeSpectrumEquiv hζ).symm (f * primeSpectrumEquiv hζ v) := rfl

/-- The Fourier values of the ordinary conjugate are pointwise eigenvalues. -/
theorem primeSpectrumEquiv_multiplier (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (f v : PrimeSpectrumDigits ι ℓ → K) (ω : PrimeSpectrumDigits ι ℓ) :
    primeSpectrumEquiv hζ (primeSpectrumMultiplier hζ f v) ω = f ω * primeSpectrumEquiv hζ v ω := by
  rw [primeSpectrumMultiplier_apply, LinearEquiv.apply_symm_apply, Pi.mul_apply]

/-- Ordinary matrix entries are the inversion sum at the input minus the output. -/
theorem primeSpectrumMultiplier_matrix (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (f : PrimeSpectrumDigits ι ℓ → K) (s x : PrimeSpectrumDigits ι ℓ) :
    (primeSpectrumMultiplier hζ f).toMatrix' s x = (⅟ (ℓ : K)) ^ (2 * Fintype.card ι) *
      ∑ X : ι → ZMod ℓ, ∑ Z : ι → ZMod ℓ,
        digitPhase hζ (∑ i, ((x.1 i - s.1 i) * X i + (x.2 i - s.2 i) * Z i)) * f (X, Z) := by
  rw [LinearMap.toMatrix'_apply, primeSpectrumMultiplier_apply, primeSpectrumEquiv_symm_apply]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun Z _ => ?_
  simp only [Pi.mul_apply, primeSpectrumEquiv_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [mul_comm (f (X, Z)), ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [primeSpectrumPair, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The query whose phase exponent at the paired frequency `ω` is `k ω`. -/
def primeSpectrumQuery (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (k : PrimeSpectrumDigits ι ℓ → ZMod ℓ) :
    Module.End K (PrimeSpectrumDigits ι ℓ → K) :=
  primeSpectrumMultiplier hζ (fun ω => digitPhase hζ (k ω))

theorem primeSpectrumEquiv_query (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (k : PrimeSpectrumDigits ι ℓ → ZMod ℓ)
    (v : PrimeSpectrumDigits ι ℓ → K) (ω : PrimeSpectrumDigits ι ℓ) :
    primeSpectrumEquiv hζ (primeSpectrumQuery hζ k v) ω =
      digitPhase hζ (k ω) * primeSpectrumEquiv hζ v ω :=
  primeSpectrumEquiv_multiplier hζ _ _ _

/-- Multiplication of spectral scalars corresponds to composition in ordinary coordinates. -/
def primeSpectrumMultiplierHom (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] :
    (PrimeSpectrumDigits ι ℓ → K) →* Module.End K (PrimeSpectrumDigits ι ℓ → K) where
  toFun := primeSpectrumMultiplier hζ
  map_one' := by ext v ω; simp [primeSpectrumMultiplier_apply]
  map_mul' f g := by ext v ω; simp [Module.End.mul_apply, primeSpectrumMultiplier_apply, mul_assoc]

theorem primeSpectrumMultiplier_pow (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (f : PrimeSpectrumDigits ι ℓ → K)
    (n : ℕ) : (primeSpectrumMultiplier hζ f) ^ n = primeSpectrumMultiplier hζ (f ^ n) :=
  ((primeSpectrumMultiplierHom hζ).map_pow f n).symm

/-- The ordered product of the ordinary queries multiplies their phases, for an arbitrary
finite family of exponents. -/
theorem primeSpectrumQuery_prod (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] {m : ℕ}
    (k : Fin m → PrimeSpectrumDigits ι ℓ → ZMod ℓ) :
    (List.ofFn fun j => primeSpectrumQuery hζ (k j)).prod =
      primeSpectrumMultiplier hζ (fun ω => ∏ j, digitPhase hζ (k j ω)) := by
  let f (j : Fin m) (ω : PrimeSpectrumDigits ι ℓ) := digitPhase hζ (k j ω)
  have h := ((primeSpectrumMultiplierHom hζ).map_list_prod (List.ofFn f)).symm
  have hf : (∏ j, f j) = fun ω => ∏ j, digitPhase hζ (k j ω) := by
    funext ω
    exact Finset.prod_apply ..
  rw [← hf]
  simpa [List.map_ofFn, List.prod_ofFn, Function.comp_def, f,
    primeSpectrumMultiplierHom, primeSpectrumQuery] using h

/-- Raising a query to a digit power multiplies its exponent by that digit. -/
theorem primeSpectrumQuery_pow (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (k : PrimeSpectrumDigits ι ℓ → ZMod ℓ)
    (a : ZMod ℓ) : (primeSpectrumQuery hζ k) ^ a.val =
      primeSpectrumQuery hζ (fun ω => a * k ω) := by
  unfold primeSpectrumQuery
  rw [primeSpectrumMultiplier_pow]
  congr 1
  funext ω
  rw [Pi.pow_apply, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem primeSpectrumQuery_pow_matrix (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (k : PrimeSpectrumDigits ι ℓ → ZMod ℓ)
    (a : ZMod ℓ) (s x : PrimeSpectrumDigits ι ℓ) :
    ((primeSpectrumQuery hζ k) ^ a.val).toMatrix' s x = (⅟ (ℓ : K)) ^ (2 * Fintype.card ι) *
      ∑ X : ι → ZMod ℓ, ∑ Z : ι → ZMod ℓ,
        digitPhase hζ (∑ i, ((x.1 i - s.1 i) * X i + (x.2 i - s.2 i) * Z i)) *
          digitPhase hζ (a * k (X, Z)) := by
  rw [primeSpectrumQuery_pow]
  exact primeSpectrumMultiplier_matrix hζ _ s x

variable {C J U : Type*} [Fintype C] [Fintype J] [Fintype U]

/-- The repaired product has the ordinary matrix of the unshifted quadratic tuple query. -/
theorem primeSpectrumQueryProduct_matrix (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (hm : Fintype.card J ≡ 1 [MOD ℓ]) :
    (primeSpectrumMultiplier hζ (fun ω : PrimeSpectrumDigits (C × (J ⊕ U)) ℓ =>
      ∏ j, primeQueryMultiplier (digitPhase hζ) (Function.curry ω.1) (Function.curry ω.2) j)).toMatrix' =
      Matrix.of (fun s x => primeTupleKernelRing hζ x.1 x.2 s.1 s.2) := by
  let f (ω : PrimeSpectrumDigits (C × (J ⊕ U)) ℓ) :=
    ∏ j, primeQueryMultiplier (digitPhase hζ) (Function.curry ω.1) (Function.curry ω.2) j
  ext s x
  refine (primeSpectrumMultiplier_matrix hζ f s x).trans ?_
  rw [Matrix.of_apply, ← primeQueryProduct_kernel_ring hζ hm x.1 x.2 s.1 s.2]
  congr 1
  refine Finset.sum_congr (by ext; simp) fun X _ => ?_
  exact Finset.sum_congr (by ext; simp) fun Z _ => rfl

/-- Composing the ordinary query operators for all distinguished digits gives
the quadratic tuple kernel, including its Fourier-inversion normalization. -/
theorem primeSpectrumQuery_prod_matrix {m : ℕ} (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (hm : m ≡ 1 [MOD ℓ]) :
    (List.ofFn (fun j : Fin m => primeSpectrumQuery hζ
      (fun ω : PrimeSpectrumDigits (C × (Fin m ⊕ U)) ℓ =>
        primeQueryExponent (Function.curry ω.1) (Function.curry ω.2) j))).prod.toMatrix' =
        Matrix.of (fun s x => primeTupleKernelRing hζ x.1 x.2 s.1 s.2) := by
  let k (j : Fin m) (ω : PrimeSpectrumDigits (C × (Fin m ⊕ U)) ℓ) :=
    primeQueryExponent (Function.curry ω.1) (Function.curry ω.2) j
  exact (congrArg LinearMap.toMatrix' (primeSpectrumQuery_prod hζ k)).trans
    (primeSpectrumQueryProduct_matrix (C := C) (J := Fin m) (U := U) hζ (by simpa using hm))

end

end

end FiniteFourier
end LinearAlgebra
end OAI
