import OAI.Computability.BorderVNP.BranchSpecializationConstants
import OAI.LinearAlgebra.SpectralBooks.SquareExponent

namespace OAI
/-! # Reduction of uniform square-exponent lower bounds to finite fields

Every fixed rank decomposition of an integral tensor is a solution to a finite
system of integer polynomial equations. A finite residue field preserves that
solution's rank bound. One may choose a different residue field for each tensor
power when the lower bound is uniform over finite fields.
-/

namespace ThreeFlat

open MatrixMultiplication.Foundation LinearAlgebra.SpectralBooks MvPolynomial

private theorem exists_finite_specialization {I : Type} [Fintype I]
    (K : Type*) [Field K] (a : I → K) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (v : I → E),
      ∀ f : MvPolynomial I ℤ, eval₂Hom (Int.castRingHom K) a f = 0 →
        eval₂Hom (Int.castRingHom E) v f = 0 := by
  classical
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hz
  · obtain ⟨E, fE, _, hE, v, hv, _⟩ :=
      Computability.BorderVNP.Specialization.exists_finiteField_realization K _ hp a ∅ (by simp)
    exact ⟨E, fE, hE, v, hv⟩
  · let : CharZero K := (CharP.ringChar_zero_iff_CharZero K).mp hz
    obtain ⟨d, k, hd, hred⟩ :=
      Computability.BorderVNP.Specialization.exists_fixed_constants_reduction K a ∅ (by simp)
    obtain ⟨p, hlarge, hp⟩ := Nat.exists_infinite_primes (d.natAbs + 1)
    have hpd : ¬ (p : ℤ) ∣ d := by
      intro h
      have h' : p ∣ d.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr h
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) h'
      omega
    obtain ⟨E, fE, _, hE, v, _, hv, _⟩ := hred p hp hpd
    exact ⟨E, fE, hE, v, hv⟩

/-- The rank of an integral three-tensor over some finite field is at most its
rank over the given field. -/
theorem exists_finite_field_rank_le {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) (K : Type*) [Field K] :
    ∃ (E : Type) (_ : Field E) (_ : Finite E),
      tensorRank (fun x y z => (T x y z : E)) ≤ tensorRank (fun x y z => (T x y z : K)) := by
  classical
  let r := tensorRank (fun x y z => (T x y z : K))
  obtain ⟨A, B, C', h⟩ := rankAtMost_tensorRank (fun x y z => (T x y z : K))
  let v : Fin r × (X ⊕ Y ⊕ Z) → K := fun p => p.2.elim (A p.1) (Sum.elim (B p.1) (C' p.1))
  obtain ⟨E, fE, hE, w, hw⟩ := exists_finite_specialization K v
  refine ⟨E, fE, hE, tensorRank_le_of_rankAtMost ?_⟩
  refine ⟨fun i x => w (i, .inl x), fun i y => w (i, .inr (.inl y)),
    fun i z => w (i, .inr (.inr z)), ?_⟩
  funext x y z
  let eqn : MvPolynomial (Fin r × (X ⊕ Y ⊕ Z)) ℤ :=
    C (T x y z) - ∑ i, MvPolynomial.X (i, .inl x) *
      MvPolynomial.X (i, .inr (.inl y)) * MvPolynomial.X (i, .inr (.inr z))
  have valid : eval₂Hom (Int.castRingHom K) v eqn = 0 := by
    simpa only [eqn, map_sub, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X', Int.coe_castRingHom, v,
      Sum.elim_inl, Sum.elim_inr, Tensor.rankOne, sub_eq_zero] using congrFun (congrFun (congrFun h x) y) z
  simpa only [eqn, map_sub, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X', Int.coe_castRingHom,
    Tensor.rankOne, sub_eq_zero] using hw eqn valid

private theorem intCast_matrixCoefficients (F : Type*) [Field F] (x y z : ℕ) :
    (fun a b c => (Tensor.matrixCoefficients (K := ℤ) (Fin z) (Fin x) (Fin y) a b c : F))
      = matrixTensor F x y z := by
  funext a b c
  dsimp only [matrixTensor, Tensor.matrixCoefficients]
  split <;> simp

theorem exists_finite_field_matrixRank_le (K : Type*) [Field K] (x y z : ℕ) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E),
      tensorRank (matrixTensor E x y z) ≤ tensorRank (matrixTensor K x y z) := by
  let T := Tensor.matrixCoefficients (K := ℤ) (Fin z) (Fin x) (Fin y)
  obtain ⟨E, fE, hE, h⟩ := exists_finite_field_rank_le T K
  refine ⟨E, fE, hE, ?_⟩
  simpa only [T, intCast_matrixCoefficients] using h

/-- Any constant which lower-bounds the square exponent over every finite
field also lower-bounds it over an arbitrary field. -/
theorem square_exponent_lower_bound_of_finite_fields {c : ℝ}
    (finite_bound : ∀ (E : Type) [Field E] [Finite E], c ≤ formalOmega E 1 1 1)
    (F : Type*) [Field F] : c ≤ formalOmega F 1 1 1 := by
  apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp
  change ((2 : ℕ) : ℝ) ^ c ≤ ((2 : ℕ) : ℝ) ^ formalOmega F 1 1 1
  rw [← square_asymptoticRank_eq_rpow_formalOmega F (by decide : 2 ≤ 2)]
  apply le_ciInf
  intro k
  rw [tensorRank_matrixTensor_power]
  let n := 2 ^ (k + 1)
  obtain ⟨E, fE, hE, hr⟩ := exists_finite_field_matrixRank_le F n n n
  have hn : 2 ≤ n := le_self_pow (by decide) (by omega)
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (show 0 < (k : ℝ) + 1 by positivity)).mpr
  rw [← Nat.cast_succ, Real.rpow_natCast, Real.rpow_pow_comm (by positivity), ← Nat.cast_pow]
  calc
    (n : ℝ) ^ c ≤ (n : ℝ) ^ formalOmega E 1 1 1 :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) (finite_bound E)
    _ ≤ tensorRank (matrixTensor E n n n) := rpow_formalOmega_le_tensorRank E hn
    _ ≤ tensorRank (matrixTensor F n n n) := by exact_mod_cast hr

/-- It suffices to prove a uniform square-exponent bound over prime fields
of positive characteristic. -/
theorem square_exponent_lower_bound_of_prime_fields {c : ℝ}
    (prime_bound : ∀ (p : ℕ) [Fact p.Prime], c ≤ formalOmega (ZMod p) 1 1 1)
    (F : Type*) [Field F] : c ≤ formalOmega F 1 1 1 := by
  refine square_exponent_lower_bound_of_finite_fields ?_ F
  intro E _ _
  let p := ringChar E
  let : Fact p.Prime := ⟨CharP.char_is_prime E p⟩
  have hchar : ringChar (ZMod p) = ringChar E := ringChar.eq_iff.mpr (ZMod.charP p)
  rw [← formalOmega_square_eq_of_ringChar_eq (ZMod p) E hchar]
  exact prime_bound p

end ThreeFlat

end OAI
