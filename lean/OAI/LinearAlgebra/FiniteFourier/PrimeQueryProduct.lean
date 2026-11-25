import OAI.LinearAlgebra.FiniteFourier.PrimeQueryTuple

/-! # Product of the prime-tensor query multipliers -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

variable {ℓ : ℕ} {C J U K : Type*} [Fintype C] [Fintype J] [Fintype U] [CommRing K]

/-- The distinguished digit selected by query `j` and all auxiliary digits
contribute in each column. In the manuscript `C`, `J`, and `U` have
cardinalities `f`, `m`, and `D-1`. -/
def primeQueryExponent (X Z : C → J ⊕ U → ZMod ℓ) (j : J) : ZMod ℓ :=
  ∑ c, (X c (.inl j) * Z c (.inl j) + ∑ i : U, X c (.inr i) * Z c (.inr i))

/-- Congruence of the number of distinguished digits to one makes the repeated
auxiliary terms contribute precisely once. -/
theorem sum_primeQueryExponent (hm : Fintype.card J ≡ 1 [MOD ℓ])
    (X Z : C → J ⊕ U → ZMod ℓ) :
    ∑ j, primeQueryExponent X Z j = ∑ c, ∑ i, X c i * Z c i := by
  have hc : (Fintype.card J : ZMod ℓ) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ _).2 hm
  unfold primeQueryExponent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, one_mul]

/-- The multiplier of a query at the pair of digit arrays `(X,Z)`. -/
def primeQueryMultiplier (ψ : AddChar (ZMod ℓ) K) (X Z : C → J ⊕ U → ZMod ℓ) (j : J) : K :=
  ψ (primeQueryExponent X Z j)

/-- The multiplier of the entire product is the dot-product phase. -/
theorem prod_primeQueryMultiplier (ψ : AddChar (ZMod ℓ) K) (hm : Fintype.card J ≡ 1 [MOD ℓ])
    (X Z : C → J ⊕ U → ZMod ℓ) :
    ∏ j, primeQueryMultiplier ψ X Z j = ψ (∑ c, ∑ i, X c i * Z c i) := by
  rw [← sum_primeQueryExponent hm X Z]
  exact congrArg Additive.toMul (map_sum ψ.toAddMonoidHom (primeQueryExponent X Z) _).symm

/-- For the primitive-root character the product of queries acts on each digit
pair by the single-pair multiplier of `primeQueryMatrix`. -/
theorem prod_primeQueryMultiplier_eq_prod_digitPhase [NeZero ℓ] {ζ : K}
    (hζ : IsPrimitiveRoot ζ ℓ) (hm : Fintype.card J ≡ 1 [MOD ℓ])
    (X Z : C → J ⊕ U → ZMod ℓ) :
    ∏ j, primeQueryMultiplier (digitPhase hζ) X Z j =
      ∏ c, ∏ i, digitPhase hζ (X c i * Z c i) := by
  rw [prod_primeQueryMultiplier _ hm]
  simp_rw [digitPhase_sum]

open scoped Classical in
/-- Fourier inversion of the product of the query multipliers on all frequency
tuples gives the ordinary kernel of the quadratic dot-product phase. -/
theorem primeQueryProduct_kernel_ring [NeZero ℓ] [Invertible (ℓ : K)] {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hm : Fintype.card J ≡ 1 [MOD ℓ]) (x y s t : C × (J ⊕ U) → ZMod ℓ) :
    (⅟ (ℓ : K)) ^ (2 * Fintype.card (C × (J ⊕ U))) *
        (∑ X : C × (J ⊕ U) → ZMod ℓ, ∑ Z : C × (J ⊕ U) → ZMod ℓ,
          digitPhase hζ (∑ i, ((x i - s i) * X i + (y i - t i) * Z i)) *
            ∏ j, primeQueryMultiplier (digitPhase hζ) (Function.curry X) (Function.curry Z) j) =
      primeTupleKernelRing hζ x y s t := by
  unfold primeTupleKernelRing
  congr 1
  refine Finset.sum_congr (by ext; simp) fun X _ ↦ ?_
  refine Finset.sum_congr (by ext; simp) fun Z _ ↦ ?_
  rw [prod_primeQueryMultiplier _ hm, ← AddChar.map_add_eq_mul]
  simp only [Finset.sum_add_distrib, Fintype.sum_prod_type, Function.curry_apply]

open scoped Classical in
/-- Fourier inversion of the product of the query multipliers on all frequency
tuples gives the ordinary kernel of the quadratic dot-product phase. -/
theorem primeQueryProduct_kernel {E : Type*} [Field E] [NeZero ℓ] {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ)
    (hm : Fintype.card J ≡ 1 [MOD ℓ]) (x y s t : C × (J ⊕ U) → ZMod ℓ) :
    (ℓ : E)⁻¹ ^ (2 * Fintype.card (C × (J ⊕ U))) *
        (∑ X : C × (J ⊕ U) → ZMod ℓ, ∑ Z : C × (J ⊕ U) → ZMod ℓ,
          digitPhase hζ (∑ i, ((x i - s i) * X i + (y i - t i) * Z i)) *
            ∏ j, primeQueryMultiplier (digitPhase hζ) (Function.curry X) (Function.curry Z) j) =
      primeTupleKernel hζ x y s t  := by
  let := invertibleOfNonzero hζ.neZero'.out
  simpa [primeTupleKernel, invOf_eq_inv] using primeQueryProduct_kernel_ring hζ hm x y s t

omit [Fintype J] in
/-- In a nonempty set of columns the simultaneous spectra contain every vector
of character values. At radix two this is the sign-cube observation. -/
theorem exists_primeQueryMultiplier_eq (ψ : AddChar (ZMod ℓ) K) (c₀ : C) (b : J → ZMod ℓ) :
    ∃ X Z : C → J ⊕ U → ZMod ℓ, ∀ j, primeQueryMultiplier ψ X Z j = ψ (b j) := by
  classical
  let X : C → J ⊕ U → ZMod ℓ := fun c ↦ Sum.elim (fun _ ↦ if c = c₀ then 1 else 0) (fun _ ↦ 0)
  let Z : C → J ⊕ U → ZMod ℓ := fun _ ↦ Sum.elim b (fun _ ↦ 0)
  refine ⟨X, Z, fun j ↦ ?_⟩
  simp [primeQueryMultiplier, primeQueryExponent, X, Z, ite_mul]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
