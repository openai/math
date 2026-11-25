import OAI.Computability.IntegerMultiplication.Bits.Small
import OAI.Computability.IntegerMultiplication.Partial
import OAI.Computability.NearSquareRoot.ScheduleFence

/-!
# Sequential digit operations for a fenced attempt

The chunk addresses and widths travel on tape as unary cursors. Each operation
uses one fixed P192 program for every cursor length.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkArithmetic

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits

/-- Read a little-endian operand starting at the supplied offset. Return
exactly the requested width, in the external multiplier's MSF order. -/
def extract (p : Tally × Tally × Word) : Word :=
  (resize (p.2.1, (cutLists (p.1, p.2.2)).2)).reverse

theorem easy_extract : Easy extract := by
  unfold extract
  apply easy_reverse
  apply easy_resize
  apply Easy.pair (by fun_prop)
  exact (easy_cut (g := fun p : Tally × Tally × Word => (p.1, p.2.2)) (by fun_prop)).sndCompose

private theorem eq_tally_length (u : Tally) : u = tally u.length := by
  induction u with
  | nil => rfl
  | cons a l ih => simpa [List.length_cons] using congrArg (() :: ·) ih

private theorem value_drop (d : ℕ) (x : Word) : value (x.drop d) = value x / 2 ^ d := by
  induction d generalizing x with
  | zero => simp
  | succ k ih =>
    cases x with
    | nil => simp
    | cons a l =>
      rw [List.drop_succ_cons, ih, pow_succ', ← Nat.div_div_eq_div_mul, value_half]

theorem extract_length (o u : Tally) (x : Word) :
    (extract (o,u,x)).length = u.length := by
  change (resize (u, x.drop o.length)).reverse.length = u.length
  rw [List.length_reverse, show resize (u, x.drop o.length) = sized u.length (x.drop o.length)
    from congrArg (fun t => resize (t, x.drop o.length)) (eq_tally_length u), sized_length]

theorem extract_value (o u : Tally) (x : Word) :
    bitValue (extract (o,u,x)) = value x / 2 ^ o.length % 2 ^ u.length := by
  rw [endianness, extract, List.reverse_reverse]
  change value (resize (u, x.drop o.length)) = _
  rw [show resize (u, x.drop o.length) = sized u.length (x.drop o.length)
    from congrArg (fun t => resize (t, x.drop o.length)) (eq_tally_length u)]
  rw [sized_low, value_drop]

/-- At offset `i*u`, the input to the digit multiplier is exactly the digit
with index `i` in the base used by the reconstruction theorem. -/
theorem extract_chunkDigit (o u : Tally) (x : Word) (i : ℕ) (h : o.length = i*u.length) :
    bitValue (extract (o,u,x)) = Uniform.chunkDigit (2 ^ u.length) (value x) i := by
  rw [extract_value, Uniform.chunkDigit, ← pow_mul, h, Nat.mul_comm i]

/-- Add an MSF product at a runtime bit shift to a fixed-width LE accumulator. -/
def accumulate (p : Tally × Word × Word) : Word :=
  resize (ruler p.2.2, add (p.2.2, shift (p.1, p.2.1.reverse)))

theorem easy_accumulate : Easy accumulate := by unfold accumulate; fun_prop

private theorem accumulate_eq (o : Tally) (z a : Word) :
    accumulate (o,z,a) = sized a.length (add (a, shift (o,z.reverse))) := by
  change resize (ruler a, _) = _
  have h : ruler a = tally a.length := by simp [ruler, tally]
  rw [h]
  rfl

theorem accumulate_length (o : Tally) (z a : Word) :
    (accumulate (o,z,a)).length = a.length := by simp [accumulate_eq]

theorem accumulate_value (o : Tally) (z a : Word) :
    value (accumulate (o,z,a)) = (value a + 2 ^ o.length * bitValue z) % 2 ^ a.length := by
  rw [accumulate_eq, sized_low, add_val, shift_value, endianness]

theorem accumulate_exact (o : Tally) (z a : Word)
    (h : value a + 2 ^ o.length * bitValue z < 2 ^ a.length) :
    value (accumulate (o,z,a)) = value a + 2 ^ o.length * bitValue z := by
  rw [accumulate_value, Nat.mod_eq_of_lt h]

end ChunkArithmetic

end NearSquareRoot
end Computability
end OAI
