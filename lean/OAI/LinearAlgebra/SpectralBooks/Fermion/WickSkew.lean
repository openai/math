import OAI.LinearAlgebra.SpectralBooks.Fermion.WickFields

/-! # Exchange of blocks in a normal-ordered fermion word

Exchanging adjacent fields inside a normal product negates it. Consequently,
two consecutive blocks may be exchanged with sign `(-1)^(length₁*length₂)`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

variable (k : Type*) {α E : Type*} [CommRing k] [Ring E] [Algebra k E]
variable (C A : α → E)
variable (hcc : ∀ x y, C x * C y + C y * C x = 0)
variable (haa : ∀ x y, A x * A y + A y * A x = 0)

private theorem normal_prefix_smul (p l r : List α) (a : k) (hlen : l.length = r.length)
    (h : normal k C A l = a • normal k C A r) :
    normal k C A (p ++ l) = a • normal k C A (p ++ r) := by
  induction p with
  | nil => exact h
  | cons x p ih =>
    simp only [List.cons_append, normal, ih, List.length_append, hlen,
      mul_smul_comm, smul_mul_assoc, smul_add]
    rw [smul_comm]

include hcc haa in
/-- Adjacent exchange in any context of the word. -/
theorem normal_swap_adjacent (p : List α) (x y : α) (s : List α) :
    normal k C A (p ++ x :: y :: s) = -normal k C A (p ++ y :: x :: s) := by
  have hc := eq_neg_of_add_eq_zero_left (hcc x y)
  have ha := eq_neg_of_add_eq_zero_left (haa y x)
  rw [← neg_one_smul k]
  apply normal_prefix_smul <;> try rfl
  simp only [normal, one_smul, List.length_cons, pow_succ, mul_neg, mul_one, neg_smul,
    mul_add, add_mul, smul_add, mul_smul_comm, smul_mul_assoc, ← mul_assoc (C x) (C y), hc,
    neg_mul, mul_assoc, ha, smul_neg]
  abel

include hcc haa in
private theorem normal_move_one (p : List α) (x : α) (r s : List α) :
    normal k C A (p ++ x :: (r ++ s)) =
      (-1 : k) ^ r.length • normal k C A (p ++ r ++ x :: s) := by
  induction r generalizing p with
  | nil => simp
  | cons y r ih =>
    simp only [List.cons_append, List.length_cons, pow_succ, mul_neg, mul_one, neg_smul]
    rw [normal_swap_adjacent k C A hcc haa]
    simpa [List.append_assoc] using congrArg Neg.neg (ih (p ++ [y]))

include hcc haa in
/-- Exchange of consecutive subwords with an arbitrary prefix and suffix. -/
theorem normal_swap_blocks (p l r s : List α) :
    normal k C A (p ++ l ++ r ++ s) =
      (-1 : k) ^ (l.length * r.length) • normal k C A (p ++ r ++ l ++ s) := by
  induction l generalizing p with
  | nil => simp
  | cons x l ih =>
    have step₁ := ih (p ++ [x])
    have step₂ := normal_move_one k C A hcc haa p x r (l ++ s)
    simp only [List.append_assoc, List.nil_append, List.cons_append] at step₁
    simp only [List.append_assoc, List.length_cons, Nat.succ_mul, pow_add, List.cons_append] at step₂ ⊢
    rw [step₁, step₂, smul_smul]

include hcc haa in
/-- Exchange the two blocks of a normal-ordered word. -/
theorem normal_append_swap (l r : List α) :
    normal k C A (l ++ r) = (-1 : k) ^ (l.length * r.length) • normal k C A (r ++ l) := by
  simpa using normal_swap_blocks k C A hcc haa [] l r []

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
