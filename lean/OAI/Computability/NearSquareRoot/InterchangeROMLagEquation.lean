import OAI.Computability.IntegerMultiplication.Adic.Suffix

/-! # Directed natural-number congruences for signed address opcodes

Clearing a span's denominator gives two nonnegative affine forms with the
same remainder. A negative width reverses the input digit order by mirroring
its address, which contributes the numerator as a constant offset.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ROMLagEquation

open IntegerMultiplication.Port IntegerMultiplication.Adic

variable {b f : ℕ}

theorem slopes_coprime (s : Span b) (f : ℕ) :
    Nat.Coprime s.top.count (b ^ f) ∧ Nat.Coprime s.down.count (b ^ f) :=
  ⟨s.top.side.pow_right f, s.down.side.pow_right f⟩

private theorem clear_den (s : Span b) :
    (s.down.count : Tower b f) * s.land f =
      (if s.neg then -1 else 1 : Tower b f) * s.top.count := by
  have h : s.down.own f * s.fold f = Span.polarity b f s.neg * s.top.own f := by
    rw [mul_comm, Span.fold, mul_assoc, inv_mul_cancel, mul_one]
  cases hs : s.neg <;>
    simpa [Span.land, Span.polarity, hs] using congrArg Units.val h

variable [NeZero b]

theorem width_pos (s : Span b) (h : s.neg = false) (x : Block b f) :
    s.top.count * number x % b ^ f = s.down.count * number (sweep s f x) % b ^ f := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  simp only [Nat.cast_mul, ← idx_nat, inj, ← mul_assoc, clear_den, h,
    Bool.false_eq_true, ite_false, one_mul]

theorem width_neg (s : Span b) (h : s.neg = true) (x : Block b f) :
    (s.top.count * number x + s.top.count) % b ^ f =
      s.down.count * number (sweep s f (mirror x)) % b ^ f := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  simp only [Nat.cast_add, Nat.cast_mul, ← idx_nat, inj, reflects, ← mul_assoc, clear_den, h,
    ite_true, neg_one_mul]
  ring

/-- The optional operand is exactly the signed span used when computing the glide offset. -/
private theorem gather_index (s : Span b) (c x : Block b f) :
    index b f (glide (Pinpoint.stamp f (some s) * index b f c) x) =
      index b f x + s.land f * index b f c := move_nat _ _

theorem gather_pos (s : Span b) (h : s.neg = false) (c x : Block b f) :
    (s.down.count * number x + s.top.count * number c) % b ^ f =
      s.down.count * number (glide (Pinpoint.stamp f (some s) * index b f c) x) % b ^ f := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  simp only [Nat.cast_add, Nat.cast_mul, ← idx_nat, gather_index, mul_add, ← mul_assoc, clear_den, h,
    Bool.false_eq_true, ite_false, one_mul]

theorem gather_neg (s : Span b) (h : s.neg = true) (c x : Block b f) :
    s.down.count * number x % b ^ f =
      (s.down.count * number (glide (Pinpoint.stamp f (some s) * index b f c) x) +
        s.top.count * number c) % b ^ f := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  simp only [Nat.cast_add, Nat.cast_mul, ← idx_nat, gather_index, mul_add, ← mul_assoc, clear_den, h,
    ite_true, neg_one_mul]
  ring

@[simp] theorem gather_none (c x : Block b f) :
    glide (Pinpoint.stamp f (none : Pinpoint b) * index b f c) x = x := by
  apply (index b f).injective
  simp only [move_nat, Pinpoint.none, zero_mul, add_zero]

end ROMLagEquation

end NearSquareRoot
end Computability
end OAI
