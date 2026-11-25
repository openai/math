import Mathlib.Tactic

/-! # Normal-ordered fields and single contractions

The creator and annihilator parts of each field take values in an associative
algebra. Commuting an annihilator through a normal product produces one term
for each removed field, with a sign determined by its position.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open scoped BigOperators

variable {α k E : Type*} [CommRing k] [Ring E] [Algebra k E]

/-- Normal ordering puts the creator part of the first field on the left and
its annihilator part on the right, crossing every remaining field. -/
def normal (k : Type*) [CommRing k] [Algebra k E] (C A : α → E) : List α → E
  | [] => 1
  | f :: r => C f * normal k C A r + (-1 : k) ^ r.length • (normal k C A r * A f)

private def contractions (C A : α → E) (κ : α → α → k) (x : α) (r : List α) : E :=
  ∑ j : Fin r.length, ((-1 : k) ^ j.val * κ x r[j.val]) • normal k C A (r.eraseIdx j.val)

private theorem contractions_cons (C A : α → E) (κ : α → α → k) (x f : α) (r : List α) :
    contractions C A κ x (f :: r) = κ x f • normal k C A r -
      C f * contractions C A κ x r +
      (-1 : k) ^ r.length • (contractions C A κ x r * A f) := by
  classical
  unfold contractions
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, List.getElem_cons_zero, List.eraseIdx_zero,
    Fin.val_succ, List.getElem_cons_succ, List.eraseIdx_cons_succ, normal, Finset.mul_sum,
    Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib, sub_eq_add_neg, add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hlen : (r.eraseIdx j.val).length + 1 = r.length := by
    have hj := j.isLt
    rw [List.length_eraseIdx_of_lt j.isLt]
    omega
  have hsign : (-1 : k) ^ r.length = -((-1 : k) ^ (r.eraseIdx j.val).length) := by
    conv_lhs => rw [← hlen, pow_succ]
    simp
  simp [hsign, pow_succ, smul_add, smul_smul, mul_comm,
    mul_left_comm]

/-- The one-annihilator Wick identity. The summand with index `j` contracts
the annihilator against the field at position `j`. -/
theorem ann_mul_normal (C A : α → E) (κ : α → α → k)
    (hac : ∀ x y, A x * C y + C y * A x = algebraMap k E (κ x y))
    (haa : ∀ x y, A x * A y + A y * A x = 0) (x : α) (r : List α) :
    A x * normal k C A r = (-1 : k) ^ r.length • (normal k C A r * A x) +
      ∑ j : Fin r.length, ((-1 : k) ^ j.val * κ x r[j.val]) • normal k C A (r.eraseIdx j.val) := by
  change _ = _ + contractions C A κ x r
  induction r with
  | nil => simp [normal, contractions]
  | cons f r ih =>
    have hc := eq_sub_of_add_eq (hac x f)
    have ha := eq_neg_of_add_eq_zero_left (haa x f)
    rw [contractions_cons, normal, List.length_cons, pow_succ]
    simp only [mul_neg, mul_one, neg_smul, mul_add, mul_smul_comm, ← mul_assoc (A x), hc,
      sub_mul, mul_assoc (C f), ih, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      add_mul, smul_add, mul_assoc, ha, mul_neg, smul_neg]
    abel

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
