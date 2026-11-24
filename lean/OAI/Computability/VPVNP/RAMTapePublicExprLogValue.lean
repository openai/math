import OAI.Computability.VPVNP.RAMTapeUnaryWordValue
import Mathlib.Data.Nat.Log

/-! # Logarithms of a padded binary word

A nonzero little-endian word has a unique highest set bit. Its lower bits
determine whether the ceiling exceeds the floor by one.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicExprLog

open TapeWord

theorem split_word (xs : List Bool) :
    xs = List.replicate xs.length false ∨ ∃ low z, xs = low ++ true :: List.replicate z false := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons b xs ih =>
    rcases ih with h | ⟨low,z,rfl⟩
    · cases b
      · exact Or.inl (congrArg (false :: ·) h)
      · exact Or.inr ⟨[], xs.length, congrArg (true :: ·) h⟩
    · exact Or.inr ⟨b::low, z, rfl⟩

private theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih => simp [value, ih, pow_succ]; ring

private theorem contains_one (xs : List Bool) : xs.contains true = true ↔ 0 < value xs := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    cases b <;> simp [value] at ih ⊢
    exact ih

theorem log_split (ceiling : Bool) (low : List Bool) (z : ℕ) :
    let x := value (low ++ true :: List.replicate z false)
    (if ceiling then Nat.clog 2 x else Nat.log 2 x) =
      low.length + (ceiling && low.contains true).toNat := by
  dsimp only
  rw [value_append]
  simp only [value, Bool.toNat_true, UnaryWord.zeros_value, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  have hlt := value_lt low
  have htop : value low + 2 ^ low.length < 2 ^ (low.length + 1) := by rw [pow_succ]; omega
  cases ceiling with
  | false => simpa using Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_left ..) htop
  | true =>
    cases hb : low.contains true
    · have hv : value low = 0 := by
        have hn : ¬0 < value low := fun h ↦ Bool.false_ne_true (hb.symm.trans ((contains_one low).mpr h))
        omega
      simp [hv, Nat.clog_pow _ _ (by decide : 1 < 2)]
    · have hv := (contains_one low).mp hb
      have hu := Nat.clog_le_of_le_pow htop.le
      have hl : ¬ Nat.clog 2 (value low + 2 ^ low.length) ≤ low.length := by
        rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
        omega
      simp only [Bool.true_and, Bool.toNat_true, ite_true]
      omega

end RAMTape.PublicExprLog

end VPVNP
end Computability
end OAI
