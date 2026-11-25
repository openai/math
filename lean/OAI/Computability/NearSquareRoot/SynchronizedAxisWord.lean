import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Encoded instructions for one short-axis transform

The first unary field selects one of ten instructions. Its argument, when
used, is a radix-bit position. The Boolean selects the adjoint. Instructions
appear in matrix multiplication order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord
open IntegerMultiplication.Code

abbrev Inst := Tally × Tally × Bool

/-- An instruction in forward orientation. -/
def inst (tag : ℕ) (arg : Tally := []) : Inst := (tally tag, arg, false)

def flip (x : Inst) : Inst := (x.1, x.2.1, !x.2.2)
def adj (w : List Inst) : List Inst := w.reverse.map flip

/-- Bit reversal (0), twiddle (1), normalized butterfly (2). -/
def radix (k : Tally) : List Inst :=
  inst 0 :: (Iter.lineup k).reverse.flatMap (fun i => [inst 1 i, inst 2 i])

/-- The two-coordinate chirp dilation (3) and outer quadratic phase (4). -/
def dilate (k : Tally) : List Inst :=
  [inst 4] ++ adj (radix k) ++ [inst 3] ++ radix k ++ [inst 4]

/-- Bare positive and negative active-coordinate reflections (5 and 6). -/
def reflections (k : Tally) : List Inst :=
  dilate k ++ [inst 5] ++ adj (dilate k) ++ [inst 6]

def amplify (k : Tally) : List Inst :=
  (List.replicate 64 (reflections k)).flatten ++ dilate k

/-- Final three phase diagonals (7, 8, 9) restore the borrowed complement. -/
def restored (k : Tally) : List Inst :=
  [inst 7] ++ adj (amplify k) ++ [inst 8] ++ amplify k ++ [inst 9]

end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
