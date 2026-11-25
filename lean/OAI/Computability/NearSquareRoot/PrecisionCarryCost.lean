import OAI.Computability.IntegerMultiplication.Bits.Word
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith

/-! # Encoded size of the carry pass

The input tree of the P192 carry/output pass includes a unary ruler for the
output width and one unary radix-width ruler for each coefficient. This bound
charges all those symbols and all list and product constructors.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication.Code IntegerMultiplication.Bits

private theorem sizeListLe {α : Type*} [Codec α] (xs : List α) (w : ℕ)
    (h : ∀ x ∈ xs, size x ≤ w) :
    size xs ≤ xs.length * (w+1) + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    rw [size_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Size of the exact tuple consumed by the P192 carry pass, including every
unary ruler. Each coefficient word is allowed its own length. -/
theorem carryInputSize {m n b d : ℕ} (x : Fin m → Word)
    (hw : ∀ i, (x i).length ≤ d*b) :
    size (tally (2*n), List.ofFn x, List.replicate m (tally b), tally b) ≤
      4*n + m*(2*(d*b)+2) + m*(2*b+2) + 2*b + 7 := by
  have hx := sizeListLe (List.ofFn x) (2*(d*b)+1) (by
    rw [List.forall_mem_ofFn_iff]
    intro i
    rw [size_word]
    have h := hw i
    omega)
  have hr := sizeListLe (List.replicate m (tally b)) (2*b+1) (by
    intro r h
    obtain rfl := List.eq_of_mem_replicate h
    simp [size_tally, tally_length])
  simp only [List.length_ofFn, List.length_replicate, Nat.add_assoc, Nat.reduceAdd] at hx hr
  simp only [size_prod, size_tally, tally_length]
  omega

/-- The manuscript's bounds `m ≤ N`, `b ≤ 2k` and `n ≤ Nk` give a linear
bound in the physical volume of the padded stream. The constant depends only
on the fixed number of radix digits allowed per coefficient. -/
theorem carryInputSize_le_volume {m n b d N k : ℕ} (x : Fin m → Word)
    (hw : ∀ i, (x i).length ≤ d*b) (hm : m ≤ N) (hb : b ≤ 2*k)
    (hn : n ≤ N*k) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    size (tally (2*n), List.ofFn x, List.replicate m (tally b), tally b) ≤
      (4*d+23) * (N*k) := by
  apply (carryInputSize x hw).trans
  have hvol : 1 ≤ N*k := Nat.mul_pos hN hk
  have hwidth : k ≤ N*k := Nat.le_mul_of_pos_left _ hN
  have hcount : N ≤ N*k := Nat.le_mul_of_pos_right _ hk
  have h1 := Nat.mul_le_mul hm hb
  have h2 := Nat.mul_le_mul_left d h1
  nlinarith

end NearSquareRoot
end Computability
end OAI
