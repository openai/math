import Mathlib.RingTheory.Nullstellensatz

/-!
# Descent of exact polynomial computations

Section 1 of *VP and VNP differ over every field* passes from a circuit over an
arbitrary field to the same circuit topology over the algebraic closure of the prime
field. Each scalar input of the topology can first be replaced by a parameter. The
coefficients of the resulting formal output are polynomials in these parameters.
Hilbert's Nullstellensatz descends the simultaneous coefficient equations to any
algebraically closed extension of the base field.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {k F K σ υ : Type*} [Field k] [Field F] [Field K]
    [Algebra k F] [Algebra k K] [IsAlgClosed K] [Finite σ]

/-- A polynomial system in finitely many unknowns that has a solution in an extension
field of `k` has a solution in every algebraically closed extension of `k`. -/
theorem polynomialSystem_descent (S : Set (MvPolynomial σ k)) (a : σ → F)
    (ha : ∀ p ∈ S, aeval a p = 0) :
    ∃ b : σ → K, ∀ p ∈ S, aeval b p = 0 := by
  have hproper : Ideal.span S ≠ ⊤ := by
    have hle : Ideal.span S ≤ vanishingIdeal k {a} :=
      Ideal.span_le.mpr fun p hp ↦ (mem_vanishingIdeal_singleton_iff a p).mpr (ha p hp)
    exact fun h ↦ (inferInstance : (vanishingIdeal k {a}).IsPrime).ne_top <|
      top_unique (h ▸ hle)
  obtain ⟨M, hM, hSM⟩ := Ideal.exists_le_maximal (Ideal.span S) hproper
  obtain ⟨b, rfl⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hM
  exact ⟨b, fun p hp ↦ (mem_vanishingIdeal_singleton_iff b p).mp
    (hSM (Ideal.subset_span hp))⟩

/-- An exact specialization of a formal output polynomial over a parameter ring descends
simultaneously in all its coefficients. This applies to a circuit with any degree of
intermediate cancellation, using its scalar inputs as the parameters. -/
theorem formalOutput_descent (P : MvPolynomial υ (MvPolynomial σ k)) (f : MvPolynomial υ k)
    (a : σ → F) (ha : map (aeval a).toRingHom P = map (algebraMap k F) f) :
    ∃ b : σ → K, map (aeval b).toRingHom P = map (algebraMap k K) f := by
  let eqn (m : υ →₀ ℕ) : MvPolynomial σ k := P.coeff m - C (f.coeff m)
  obtain ⟨b, hb⟩ := polynomialSystem_descent (K := K) (Set.range eqn) a (by
    rintro _ ⟨m, rfl⟩
    have h := congrArg (fun p : MvPolynomial υ F ↦ p.coeff m) ha
    simpa [eqn, sub_eq_zero, coeff_map] using h)
  refine ⟨b, MvPolynomial.ext _ _ fun m ↦ ?_⟩
  have h := hb (eqn m) (Set.mem_range_self m)
  simpa [eqn, sub_eq_zero, coeff_map] using h

end VPVNP
end Computability
end OAI
