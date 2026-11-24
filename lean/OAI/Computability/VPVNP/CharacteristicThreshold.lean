import OAI.Computability.VPVNP.HamiltonianHardness
import OAI.Computability.VPVNP.PermanentHardness
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Algebraic.Cardinality

/-! # The order of quantifiers in the characteristic-dependent threshold

For a fixed characteristic, an infinite collection of exceptional lengths
over possibly different fields gives infinitely many small circuits over a
single countable algebraically closed field. The field is chosen before the
exceptional lengths. This is the initial reduction in §1.2.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

universe u

theorem countable_algebraicClosure (K : Type) [Field K] [Countable K] :
    Countable (AlgebraicClosure K) :=
  Cardinal.mk_le_aleph0_iff.mp ((Algebra.IsAlgebraic.cardinalMk_le_max K (AlgebraicClosure K)).trans
    (max_le Cardinal.mk_le_aleph0 le_rfl))

/-- A prime characteristic, including the characteristic-zero case, admits
a single countable algebraically closed representative. -/
theorem exists_countable_algClosed_of_characteristic {q : ℕ} (hq : q.Prime ∨ q = 0) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K), Countable K ∧ CharP K q := by
  rcases hq with hp | rfl
  · let : Fact q.Prime := ⟨hp⟩
    exact ⟨AlgebraicClosure (ZMod q), inferInstance, inferInstance,
      countable_algebraicClosure _, inferInstance⟩
  · exact ⟨AlgebraicClosure ℚ, inferInstance, inferInstance,
      countable_algebraicClosure _, inferInstance⟩

/-- Infinitely many exceptional lengths anywhere in a fixed characteristic
produce infinitely many small circuits over the same chosen closure. -/
theorem unbounded_small_of_failure_of_uniform_bound
    {σ : ℕ → Type*} (p : (n : ℕ) → MvPolynomial (σ n) ℤ) (q C : ℕ)
    (h : ¬ ∃ N, ∀ n ≥ N, ∀ (F : Type u) [Field F] [CharP F q],
      n^C < circuitSize (map (Int.castRingHom F) (p n))) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Countable K) (_ : CharP K q),
      ∀ N, ∃ n ≥ N, circuitSize (map (Int.castRingHom K) (p n)) ≤ n^C := by
  classical
  have hq : q.Prime ∨ q = 0 := by
    by_contra hq
    exact h ⟨0, fun _ _ F _ _ => False.elim (hq (CharP.char_is_prime_or_zero F q))⟩
  obtain ⟨K, iK, hK, cnt, ch⟩ := exists_countable_algClosed_of_characteristic hq
  let := iK
  let := hK
  let := ch
  refine ⟨K, iK, hK, cnt, ch, ?_⟩
  by_contra hnone
  push Not at hnone
  obtain ⟨N, hN⟩ := hnone
  exact h ⟨N, circuitSize_intCast_uniform_bound (K := K) p q C N hN⟩

end VPVNP
end Computability
end OAI
