import OAI.Hierarchy.TaggedRadixPack
import Mathlib.Tactic

namespace OAI
/-! # Least-significant-digit passes give the full stable tagged order -/

namespace Hierarchy.Tagged.Radix
open scoped Classical
noncomputable section

/-- The real row permutation after the first `t` least-significant digits. -/
def order {n : ℕ} (base : ℕ) (key : Fin n → ℕ) : ℕ → Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | t+1 => let old := order base key t
           (Tuple.sort ((fun i => key i/base^t % base) ∘ old)).trans old

theorem field_le {p a b c d : ℕ} (al : a < p) (cl : c < p) :
    a+p*b ≤ c+p*d ↔ toLex (b,a) ≤ toLex (d,c) := by
  rw [Prod.Lex.toLex_le_toLex]
  constructor
  · intro h
    rcases lt_trichotomy b d with less | eq | more
    · exact Or.inl less
    · exact Or.inr ⟨eq, by simpa [eq] using h⟩
    · have gap := Nat.mul_le_mul_left p (show d+1 ≤ b from more)
      rw [Nat.mul_add, Nat.mul_one] at gap
      omega
  · rintro (less | ⟨eq, le⟩)
    · have gap := Nat.mul_le_mul_left p (show b+1 ≤ d from less)
      rw [Nat.mul_add, Nat.mul_one] at gap
      omega
    · have same : b=d := eq
      rw [same]
      exact Nat.add_le_add_right le _

private theorem refine_digit {n base : ℕ} (pos : 0 < base) (key : Fin n → ℕ) (t : ℕ) :
    Tuple.sort (fun i => toLex (key i/base^t % base, key i % base^t)) =
      Tuple.sort (fun i => key i % base^(t+1)) := by
  let hi := fun i => key i/base^t % base
  let lo := fun i => key i % base^t
  let pair := fun i => toLex (hi i, lo i)
  let loKey := fun i => key i % base^(t+1)
  have comp (i j) : loKey i ≤ loKey j ↔ pair i ≤ pair j := by
    dsimp [loKey,pair,hi,lo]
    rw [pow_succ, Nat.mod_mul, Nat.mod_mul]
    exact field_le (Nat.mod_lt _ (pow_pos pos _)) (Nat.mod_lt _ (pow_pos pos _))
  let e := Tuple.sort pair
  have sorted := Tuple.eq_sort_iff.mp (rfl : e = Tuple.sort pair)
  apply Tuple.eq_sort_iff.mpr
  constructor
  · exact fun i j h => (comp _ _).mpr (sorted.1 h)
  · intro i j ij eq
    exact sorted.2 i j ij (le_antisymm ((comp _ _).mp eq.le) ((comp _ _).mp eq.ge))

theorem order_prefix {n base : ℕ} (pos : 0 < base) (key : Fin n → ℕ) (t : ℕ) :
    order base key t = Tuple.sort (fun i => key i % base^t) := by
  induction t with
  | zero =>
    simp only [order, pow_zero, Nat.mod_one]
    exact (Tuple.sort_eq_refl_iff_monotone.mpr monotone_const).symm
  | succ t ih =>
    simp only [order,ih]
    exact (stable_radix_step _ _).trans (refine_digit pos key t)

theorem order_complete {n base : ℕ} (pos : 0 < base) (key : Fin n → ℕ) (t : ℕ)
    (covered : ∀ i, key i < base^t) : order base key t = Tuple.sort key := by
  simpa only [Nat.mod_eq_of_lt (covered _)] using order_prefix pos key t

/-- A record key with the flag in the least significant bit has the intended
lexicographic order on address first and source/target second. -/
theorem flagged_key_order (a b : ℕ) (x y : Bool) :
    2*a+x.toNat ≤ 2*b+y.toNat ↔ toLex (a,x) ≤ toLex (b,y) := by
  rw [Prod.Lex.toLex_le_toLex]
  cases x <;> cases y <;> simp <;> omega

end
end Hierarchy.Tagged.Radix

end OAI
