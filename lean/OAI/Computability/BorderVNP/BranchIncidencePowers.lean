import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Division of powers by a weighted slice polynomial

For a root `a` of `G t^(r+1) + ∑ fᵢ tⁱ`, reduce the powers of `G a` to
linear combinations of `1,a,…,a^r`. This construction needs neither division
nor an inverse of `G` and consequently commutes with every specialization.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch.Incidence

open MvPolynomial

variable {r : ℕ} {A : Type*} [CommRing A]

/-- Coefficient vector of the scaled remainder of the `j`th power of a root. -/
noncomputable def rootPowerRow (f : Fin (r+1) → A) (G : A) : ℕ → Fin (r+1) → A
  | 0 => Fin.cons 1 (fun _ => 0)
  | j+1 => fun i =>
    Fin.cons (α := fun _ => A) 0 (fun k => G * rootPowerRow f G j k.castSucc) i -
      rootPowerRow f G j (Fin.last r) * f i

/-- Evaluation of one reduced power at a root. -/
theorem sum_rootPowerRow (f : Fin (r+1) → A) (G a : A)
    (ha : G * a^(r+1) + ∑ i, f i * a^i.val = 0) (j : ℕ) :
    ∑ i, rootPowerRow f G j i * a^i.val = (G*a)^j := by
  induction j with
  | zero => simp [rootPowerRow, Fin.sum_univ_succ]
  | succ j ih =>
    let v := rootPowerRow f G j
    have hs : (∑ i : Fin (r+1), (Fin.cons (α := fun _ => A) 0 (fun k => G * v k.castSucc) i) * a^i.val) =
        (G*a) * ∑ k : Fin r, v k.castSucc * a^k.val := by
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      simp only [Fin.cons_zero, zero_mul, zero_add, Fin.cons_succ, Fin.val_succ, pow_succ]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [rootPowerRow, sub_mul, Finset.sum_sub_distrib]
    change _ - ∑ i, v (Fin.last r) * f i * a^i.val = _
    rw [hs]
    have hl : ∑ i, v (Fin.last r) * f i * a^i.val = v (Fin.last r) * ∑ i, f i * a^i.val := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc ..
    rw [hl, eq_neg_of_add_eq_zero_left ((add_comm ..).trans ha), mul_neg, sub_neg_eq_add]
    rw [pow_succ' (G*a), ← ih, Fin.sum_univ_castSucc]
    change _ = G*a * ((∑ k : Fin r, v k.castSucc * a^k.val) + v (Fin.last r)*a^r)
    ring

/-- Remainder coefficients commute with specialization of the input coefficients. -/
theorem map_rootPowerRow {S : Type*} [CommRing S] (g : A →+* S)
    (f : Fin (r+1) → A) (G : A) (j : ℕ) (i : Fin (r+1)) :
    g (rootPowerRow f G j i) = rootPowerRow (g ∘ f) (g G) j i := by
  induction j generalizing i with
  | zero => exact Fin.cases (by simp [rootPowerRow]) (fun k => by simp [rootPowerRow]) i
  | succ j ih =>
    refine Fin.cases ?_ (fun k => ?_) i <;> simp [rootPowerRow, ih]

/-- A `j`th remainder coefficient has total degree at most `j*d` when
each input coefficient has degree at most `d`. -/
theorem degree_rootPowerRow {σ K : Type*} [Field K] (f : Fin (r+1) → MvPolynomial σ K)
    (G : MvPolynomial σ K) (d : ℕ) (hf : ∀ i, (f i).totalDegree ≤ d) (hG : G.totalDegree ≤ d)
    (j : ℕ) (i : Fin (r+1)) : (rootPowerRow f G j i).totalDegree ≤ j*d := by
  induction j generalizing i with
  | zero => exact Fin.cases (by simp [rootPowerRow]) (fun k => by simp [rootPowerRow]) i
  | succ j ih =>
    rw [rootPowerRow, Nat.succ_mul]
    apply (totalDegree_sub ..).trans (max_le ?_ ?_)
    · refine Fin.cases (by simp) (fun k => ?_) i
      simpa only [Fin.cons_succ, Nat.add_comm (j*d) d] using
        (totalDegree_mul G _).trans (Nat.add_le_add hG (ih k.castSucc))
    · exact (totalDegree_mul ..).trans (Nat.add_le_add (ih _) (hf _))

end Branch.Incidence

end BorderVNP
end Computability
end OAI
