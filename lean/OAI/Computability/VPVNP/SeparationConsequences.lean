import OAI.Computability.VPVNP.CharacteristicThreshold
import OAI.Computability.VPVNP.VerifierFamily

/-!
# Quantifiers and consequences of the circuit lower bound

Theorem 1.1 uses one threshold for all fields of a fixed characteristic. In
§15.1 the projection and padding argument takes place over an algebraically
closed representative of the characteristic, so the threshold for each matrix
family can also be chosen before the field.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

universe u

/-- The circuit bound in Theorem 1.1 for the paper's explicit integer family. -/
def UniformPBound : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∀ q : ℕ, ∃ N, ∀ n ≥ N, ∀ (F : Type u) [Field F] [CharP F q],
    n ^ C < circuitSize (map (Int.castRingHom F) (P n))

/-- It suffices to rule out arbitrarily large exceptional lengths in one
countable algebraic closure per characteristic. -/
theorem uniform_P_bound_of_countable_contradiction
    (h : ∀ q : ℕ, q.Prime ∨ q = 0 →
      ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Countable K) (_ : CharP K q),
        ∀ C : ℕ, 1 ≤ C → ¬ ∀ N, ∃ n ≥ N,
          circuitSize (map (Int.castRingHom K) (P n)) ≤ n ^ C) : UniformPBound.{u} := by
  intro C hC q
  by_cases hq : q.Prime ∨ q = 0
  · obtain ⟨K, iK, closed, _, ch, hn⟩ := h q hq
    specialize hn C hC
    push Not at hn
    obtain ⟨N, hN⟩ := hn
    exact ⟨N, circuitSize_intCast_uniform_bound (K := K) P q C N hN⟩
  · exact ⟨0, fun _ _ F _ _ => False.elim (hq (CharP.char_is_prime_or_zero F q))⟩

/-- Form of the reduction for a diagonal contradiction that works in every
countable algebraically closed field. -/
theorem uniform_P_bound_of_diagonal_contradiction
    (h : ∀ (C : ℕ), 1 ≤ C → ∀ (q : ℕ) (K : Type) [Field K] [IsAlgClosed K]
      [Countable K] [CharP K q],
      (∀ N, ∃ n ≥ N, circuitSize (map (Int.castRingHom K) (P n)) ≤ n ^ C) → False) :
    UniformPBound.{u} := by
  intro C hC q
  by_contra bad
  obtain ⟨K, iK, closed, count, ch, hsmall⟩ := unbounded_small_of_failure_of_uniform_bound P q C bad
  exact h C hC q K hsmall

/-- Specialize the common threshold to the characteristic of a single field. -/
theorem eventual_P_bound_of_uniform_P (h : UniformPBound.{u}) (F : Type u) [Field F] :
    EventuallySuperpolynomial fun n => circuitSize (map (Int.castRingHom F) (P n)) := by
  intro C hC
  obtain ⟨N, hN⟩ := h C hC (ringChar F)
  exact ⟨N, fun n hn => hN n hn F⟩

/-- The explicit complete family witnesses the distinction between the two
class predicates, already on families in the prescribed paired variables. -/
theorem vp_ne_vnp_of_uniform_P (h : UniformPBound.{u}) (F : Type u) [Field F] :
    (IsVP : Family F (fun n => Fin n × Bool) → Prop) ≠ IsVNP := by
  intro he
  apply not_isVP_of_eventual_size (eventual_P_bound_of_uniform_P h F)
  rw [he]
  exact P_isVNP F

/-- Corollary 1.2. The common threshold covers both matrix families in
characteristic different from two and covers directed Hamiltonian cycles in
characteristic two. The exponent zero is allowed as well. -/
theorem corollary12_of_uniform_P (h : UniformPBound.{0}) (q C : ℕ) :
    ∃ N, ∀ m ≥ N, ∀ (F : Type u) [Field F] [CharP F q],
      m ^ C < circuitSize (hamiltonianCyclePolynomial F m) ∧
        (q ≠ 2 → m ^ C < circuitSize (permanentPolynomial F m)) := by
  by_cases hq : q.Prime ∨ q = 0
  · obtain ⟨K, iK, closed, _, ch⟩ := exists_countable_algClosed_of_characteristic hq
    have hp := eventual_P_bound_of_uniform_P h K
    obtain ⟨N, hN⟩ := hamiltonian_uniform_of_P q hp C
    by_cases htwo : q = 2
    · exact ⟨N, fun m hm F _ _ => ⟨hN m hm F, fun hne => (hne htwo).elim⟩⟩
    · obtain ⟨M, hM⟩ := permanent_uniform_of_P q htwo hp C
      exact ⟨max N M, fun m hm F _ _ =>
        ⟨hN m ((le_max_left ..).trans hm) F, fun _ => hM m ((le_max_right ..).trans hm) F⟩⟩
  · exact ⟨0, fun _ _ F _ _ => False.elim (hq (CharP.char_is_prime_or_zero F q))⟩

end VPVNP
end Computability
end OAI
