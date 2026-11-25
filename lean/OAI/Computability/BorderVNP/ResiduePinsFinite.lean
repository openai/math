import OAI.Computability.BorderVNP.ResiduePinsPolynomial
import Mathlib.Data.Nat.Log

/-! # One bounded extraction power for all residue matrices

The pin vector is determined by the tests alone. The extraction power used by every matrix
can be selected once from the pole bound and the finite coefficient field. Being a power of
the field cardinality makes its inverse Frobenius the identity on every coefficient.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResiduePins

open Residue ResidueBox Module Matrix
open scoped Matrix BigOperators Classical

/-- The exact number of rows (and of columns) in (10.1). -/
theorem pin_dimension {σ β E k : Type*} [Fintype σ] [Fintype β] [Field E] [Field k]
    [Algebra k E] (B : Basis β k E) (H : ℕ) :
    Fintype.card (Index β σ H) =
      Module.finrank k E * (H + 1) ^ Fintype.card σ * (2 * H + 1) := by
  change Fintype.card (β × {e : Exponent σ // InBox H e}) = _
  rw [Fintype.card_prod, box_card, Module.finrank_eq_card_basis B]
  ac_rfl

/-- The first positive power of the ground-field cardinality above a pole budget.
The integer exponent is expressed as a power of the characteristic to use Cartier. -/
theorem exists_pin_power (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Fintype E]
    [CharP E p] [PerfectRing E p] (D : ℕ) :
    ∃ u > 0, D < p ^ u ∧ p ^ u ≤ Fintype.card E * max D 1 ∧
      (iterateFrobeniusEquiv E p u).symm.toRingHom = RingHom.id E := by
  obtain ⟨e, _, he⟩ := FiniteField.card E p
  let m := Nat.log (Fintype.card E) D + 1
  have hpow : p ^ ((e : ℕ) * m) = Fintype.card E ^ m := by rw [he, pow_mul]
  refine ⟨(e : ℕ) * m, Nat.mul_pos e.pos (Nat.succ_pos _), ?_, ?_, ?_⟩
  · rw [hpow]
    exact Nat.lt_pow_succ_log_self Fintype.one_lt_card D
  · rw [hpow, show m = Nat.log (Fintype.card E) D + 1 from rfl, pow_succ']
    apply Nat.mul_le_mul_left
    rcases D with _ | n
    · simp
    · exact (Nat.pow_log_le_self _ n.succ_ne_zero).trans (le_max_left ..)
  · ext a
    apply (iterateFrobeniusEquiv E p ((e : ℕ) * m)).injective
    change (iterateFrobeniusEquiv E p ((e : ℕ) * m))
      ((iterateFrobeniusEquiv E p ((e : ℕ) * m)).symm a) = a ^ p ^ ((e : ℕ) * m)
    rw [RingEquiv.apply_symm_apply, hpow, FiniteField.pow_card_pow]

/-- The finite residue-pin construction of Lemma 10.1 from the coordinate Cartier formula,
one trace-one test, and a common bound on the test poles. The fixed pin and power serve every
regular polynomial of the prescribed degree, and the matrices use the identity coefficient map. -/
theorem residue_pins_of_branch {σ ι β E κ : Type*} [Fintype σ] [Fintype ι] [Fintype β]
    [Field E] [Fintype E] [Field κ]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) E] [CharP E p] [PerfectRing E p]
    [Algebra (ZMod p) κ] [CharP κ p] [PerfectRing κ p]
    (φ : E →+* LaurentSeries κ) (x : σ → LaurentSeries κ) (t : (LaurentSeries κ)ˣ)
    (η₀ : LaurentSeries κ) (B : Basis β (ZMod p) E) (L D : ℕ)
    (g : ι → MvPolynomial (Option σ) E)
    (hCartier : ∀ u > 0, CartierCompatibility p φ x t η₀ u g
      (iterateFrobeniusEquiv E p u).symm.toRingHom)
    (htrace : ∃ f : Mixed σ E, tracedRes p (mixedEval φ x t f * η₀) = 1)
    (hpole : ∀ i : Index β σ (radius L (∑ j, (g j).totalDegree)),
      -(D : ℤ) ≤ (evaluate φ x t (test B i) * η₀).order) :
    let H := radius L (∑ j, (g j).totalDegree)
    let Ω := pin B H (testFunctional p φ x t η₀)
    ∃ u > 0, D < p ^ u ∧ p ^ u ≤ Fintype.card E * max D 1 ∧ (∀ a : E, a ^ (p^u) = a) ∧ (∃ i, Ω i ≠ 0) ∧
      ∀ (A : MvPolynomial σ E), A.totalDegree ≤ L → ∀ z : ZMod p,
        0 ≤ (MvPolynomial.eval₂ φ x A).order →
        (MvPolynomial.eval₂ φ x A).coeff 0 = algebraMap (ZMod p) κ z →
        (∑ μ ∈ A.support, weights B H (p ^ u) (pow_pos (Fact.out : p.Prime).pos u) g
          (RingHom.id E) (mixedIndex (polynomialIndex μ)) (A.coeff μ)) *ᵥ Ω = z • Ω := by
  obtain ⟨u, hu, hD, hbound, hroot⟩ := exists_pin_power p E D
  obtain ⟨f, hf⟩ := htrace
  have hpin := nonzero_of_trace_one p φ x t η₀ B L g _ hCartier f hf
  have hfix (a : E) : a ^ (p^u) = a := by
    have h := (iterateFrobeniusEquiv E p u).apply_symm_apply a
    have hs : (iterateFrobeniusEquiv E p u).symm a = a := RingHom.congr_fun hroot a
    rw [hs] at h
    exact h
  refine ⟨u, hu, hD, hbound, hfix, hpin, ?_⟩
  intro A hL z hr hz
  apply polynomial_eigenvector p φ x t η₀ B L u _ g (RingHom.id E) _ A hL z hr hz
  · exact fun i => le_trans (by exact_mod_cast (neg_le_neg (by exact_mod_cast hD.le : (D : ℤ) ≤ p ^ u))) (hpole i)
  · exact (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow hu.ne' p)
  · exact hroot ▸ hCartier u hu

end ResiduePins

end BorderVNP
end Computability
end OAI
