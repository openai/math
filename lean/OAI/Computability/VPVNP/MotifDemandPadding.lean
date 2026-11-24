import OAI.Computability.VPVNP.WireTensor
import Mathlib.Algebra.BigOperators.Fin

/-!
# Demand padding in a repeated wire identity

Theorem 6.1 fixes surplus bits to zero at both ends of each demand wire.
A desired index is included as the same natural number in the larger range
and read in consecutive fields of the base width. Equality at the two ends
is then equivalent to equality in every field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifDemandPadding

open WireTensor

variable {J D R : Type*} [Fintype D]

/-- Widen an index by leading zeros, then split it into `u` fields of width `a`. -/
def padFields {b u a : ℕ} (h : b ≤ u * a) : Fin (2 ^ b) ↪ (Fin u → Fin (2 ^ a)) :=
  (Fin.castLEEmb (show 2 ^ b ≤ (2 ^ a) ^ u by
    rw [← pow_mul, Nat.mul_comm a u]
    exact Nat.pow_le_pow_right (by decide) h)).trans finFunctionFinEquiv.symm.toEmbedding

/-- Each field can be read directly from the original index by division and remainder. -/
theorem padFields_digit {b u a : ℕ} (h : b ≤ u * a) (x : Fin (2 ^ b)) (i : Fin u) :
    ((padFields h x i : Fin (2 ^ a)) : ℕ) = x.val / (2 ^ a) ^ i.val % (2 ^ a) := rfl

/-- The half-wire coordinates of a binary network at a party. -/
abbrev HalfBits (src dst : D → J) (w : D → ℕ) (j : J) :=
  ((e : D) → j = src e → Fin (2 ^ w e)) × ((e : D) → j = dst e → Fin (2 ^ w e))

/-- Read the fields of a single repeated base copy at all incident half-wires. -/
def demandChunk (src dst : D → J) {b a : D → ℕ} {u : ℕ} (hab : ∀ e, b e ≤ u * a e)
    (i : Fin u) (j : J) (x : HalfBits src dst b j) : HalfBits src dst a j :=
  (fun e h ↦ padFields (hab e) (x.1 e h) i, fun e h ↦ padFields (hab e) (x.2 e h) i)

/-- The product of the repeated base demands on the padded input is exactly
the desired demand tensor. This is an entrywise identity over any coefficient
semiring, also for zero copies or zero widths. -/
theorem coeff_eq_prod_chunks [CommSemiring R] (src dst : D → J) {b a : D → ℕ} {u : ℕ}
    (hab : ∀ e, b e ≤ u * a e) (x : ∀ j, HalfBits src dst b j) :
    (wireNetwork (k := R) src dst (fun e ↦ Fin (2 ^ b e))).coeff x =
      ∏ i : Fin u, (wireNetwork (k := R) src dst (fun e ↦ Fin (2 ^ a e))).coeff
        (fun j ↦ demandChunk src dst hab i j (x j)) := by
  classical
  by_cases same : ∀ e, (x (src e)).1 e rfl = (x (dst e)).2 e rfl
  · simp [wireNetwork, demandChunk, same]
  · obtain ⟨e, he⟩ := not_forall.mp same
    have mismatch : ¬ ∀ i, padFields (hab e) ((x (src e)).1 e rfl) i =
        padFields (hab e) ((x (dst e)).2 e rfl) i :=
      fun h ↦ he ((padFields (hab e)).injective (funext h))
    obtain ⟨i, hi⟩ := not_forall.mp mismatch
    have hX : (wireNetwork (k := R) src dst (fun e ↦ Fin (2 ^ b e))).coeff x = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) (ite_eq_right (fun h ↦ (he h).elim))
    have hY : (wireNetwork (k := R) src dst (fun e ↦ Fin (2 ^ a e))).coeff
        (fun j ↦ demandChunk src dst hab i j (x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) (ite_eq_right (fun h ↦ (hi h).elim))
    exact hX.trans (Finset.prod_eq_zero (Finset.mem_univ i) hY).symm

end MotifDemandPadding

end VPVNP
end Computability
end OAI
