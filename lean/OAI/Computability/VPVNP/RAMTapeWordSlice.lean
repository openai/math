import OAI.Computability.VPVNP.RAMTapeWord

/-!
# Low and high parts of a little-endian word
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord

theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    simp only [List.cons_append, value, List.length_cons, pow_succ, ih]
    ring

@[simp] theorem value_zeros (n : ℕ) : value (List.replicate n false) = 0 := by
  induction n <;> simp [List.replicate_succ, value, *]

theorem value_take_mod (xs : List Bool) (n : ℕ) :
    value (xs.take n) = value xs % (2 ^ n) := by
  by_cases hn : n ≤ xs.length
  · have hlen : (xs.take n).length = n := by simp [List.length_take, hn]
    rw [← List.take_append_drop n xs, value_append, List.take_left' hlen, hlen,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simpa [hlen] using value_lt (xs.take n))]
  · have htake : xs.take n = xs := List.take_of_length_le (by omega)
    rw [htake, Nat.mod_eq_of_lt ((value_lt xs).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem value_take_of_lt {xs : List Bool} {n : ℕ} (h : value xs < 2 ^ n) :
    value (xs.take n) = value xs := by rw [value_take_mod, Nat.mod_eq_of_lt h]

end TapeWord

end VPVNP
end Computability
end OAI
