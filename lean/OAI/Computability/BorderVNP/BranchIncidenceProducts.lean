import OAI.Computability.BorderVNP.BranchIncidencePowers
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Remainder coefficients for a tuple of roots

Multiply the reductions of the individual root powers, padding every one
to the same denominator exponent. This leaves one coefficient for each
tuple of remainder indices and works at all points of the graph stratum.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch.Incidence

open MvPolynomial

variable {h r k : ℕ} {A : Type*} [CommRing A]

/-- A slot of the power reduction of a monomial on `h` roots and one
additional coordinate `w`. Coordinate zero is the exponent of `w`. -/
noncomputable def monomialSlot (w G : A) (f : Fin (r+1) → A) (u : Fin (h+1) → Fin (k+1))
    (l : Fin h → Fin (r+1)) : A :=
  w^(u 0).val * ∏ i, G^(k-(u i.succ).val) * rootPowerRow f G (u i.succ).val (l i)

/-- These coefficient slots commute with every specialization. -/
theorem map_monomialSlot {S : Type*} [CommRing S] (g : A →+* S) (w G : A)
    (f : Fin (r+1) → A) (u : Fin (h+1) → Fin (k+1)) (l : Fin h → Fin (r+1)) :
    g (monomialSlot w G f u l) = monomialSlot (g w) (g G) (g ∘ f) u l := by
  simp [monomialSlot, map_rootPowerRow]

/-- The sum of all evaluated slots is the original monomial multiplied by
one common power `G^(h*k)`, independent of the monomial exponents. -/
theorem sum_monomialSlot (w G : A) (f : Fin (r+1) → A) (u : Fin (h+1) → Fin (k+1))
    (a : Fin h → A) (ha : ∀ i, G * (a i)^(r+1) + ∑ l, f l * (a i)^l.val = 0) :
    (∑ l : Fin h → Fin (r+1), monomialSlot w G f u l * ∏ i, (a i)^(l i).val) =
      G^(h*k) * ∏ j, (Fin.cons (α := fun _ => A) w a j)^(u j).val := by
  have hsingle (i : Fin h) :
      (∑ l, (G^(k-(u i.succ).val) * rootPowerRow f G (u i.succ).val l) * (a i)^l.val) =
        G^k * (a i)^(u i.succ).val := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [sum_rootPowerRow f G (a i) (ha i), mul_pow, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Nat.le_of_lt_succ (u i.succ).isLt)]
  let t (i : Fin h) (l : Fin (r+1)) := G^(k-(u i.succ).val) * rootPowerRow f G (u i.succ).val l * (a i)^l.val
  have hs (l : Fin h → Fin (r+1)) : monomialSlot w G f u l * ∏ i, (a i)^(l i).val =
      w^(u 0).val * ∏ i, t i (l i) := by
    rw [monomialSlot, mul_assoc, ← Finset.prod_mul_distrib]
  simp only [hs, ← Finset.mul_sum, ← Fintype.prod_sum]
  change w^(u 0).val * (∏ i, ∑ l, t i l) = _
  have ht (i : Fin h) : ∑ l, t i l = G^k * (a i)^(u i.succ).val := hsingle i
  simp only [ht, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [← pow_mul, Nat.mul_comm k h]
  ac_rfl

/-- If the defining graph functions are affine-linear, every coefficient slot
has total degree at most `(h+1)*k` in graph coordinates. -/
theorem degree_monomialSlot {I K : Type*} [Field K] (w G : MvPolynomial I K)
    (f : Fin (r+1) → MvPolynomial I K) (hw : w.totalDegree ≤ 1) (hG : G.totalDegree ≤ 1)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (u : Fin (h+1) → Fin (k+1)) (l : Fin h → Fin (r+1)) :
    (monomialSlot w G f u l).totalDegree ≤ (h+1)*k := by
  have hp (p : MvPolynomial I K) (b : ℕ) (hp : p.totalDegree ≤ 1) : (p^b).totalDegree ≤ b := by
    exact (totalDegree_pow p b).trans (by simpa using Nat.mul_le_mul_left b hp)
  have hterm (i : Fin h) :
      (G^(k-(u i.succ).val) * rootPowerRow f G (u i.succ).val (l i)).totalDegree ≤ k := by
    have he := (totalDegree_mul ..).trans (Nat.add_le_add (hp G (k-(u i.succ).val) hG)
      (degree_rootPowerRow f G 1 hf hG (u i.succ).val (l i)))
    simpa [Nat.sub_add_cancel (Nat.le_of_lt_succ (u i.succ).isLt)] using he
  have hprod : (∏ i, G^(k-(u i.succ).val) * rootPowerRow f G (u i.succ).val (l i)).totalDegree ≤ ∑ _ : Fin h, k := (totalDegree_finsetProd ..).trans (Finset.sum_le_sum fun i _ => hterm i)
  have he := (totalDegree_mul ..).trans (Nat.add_le_add ((hp _ _ hw).trans (Nat.le_of_lt_succ (u 0).isLt)) hprod)
  simpa [monomialSlot, Nat.succ_mul, Nat.add_comm] using he

end Branch.Incidence

end BorderVNP
end Computability
end OAI
