import OAI.Computability.NearSquareRoot.BoxMask
import OAI.Computability.NearSquareRoot.BoxMaskedRecords

/-! # Five-axis descriptors for binary-to-radix interchange -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryHalo
open IntegerMultiplication Code

abbrev Header := Tally × Tally × Tally × Tally × Tally

/-- `D` is the binary field range and `E` is the common allocated range. -/
structure Shape where
  P : ℕ
  D : ℕ
  G : ℕ
  E : ℕ
  B : ℕ

structure Good (s : Shape) : Prop where
  hP : 0 < s.P
  hD : 0 < s.D
  hG : 0 < s.G
  hB : 0 < s.B
  hDE : s.D ≤ s.E

def Shape.axes (s : Shape) : List (ℕ × ℕ) :=
  [(s.P,0),(s.D,s.E-s.D),(s.G,0),(s.D,s.E-s.D),(s.B,0)]

def Shape.mask (s : Shape) := BoxOrder.expand s.axes

def Shape.header (s : Shape) : Header := (tally s.P,tally s.D,tally s.G,tally s.E,tally s.B)

def Shape.volume (s : Shape) := s.P * s.E * s.G * s.E * s.B

def Shape.denseVolume (s : Shape) := s.P * s.D * s.G * s.D * s.B

@[simp] theorem mask_length (s : Shape) (hd : s.D ≤ s.E) : s.mask.length = s.volume := by
  simp [Shape.mask, Shape.axes, Shape.volume, BoxOrder.total, Nat.add_sub_of_le hd, Nat.mul_assoc]

@[simp] theorem mask_count (s : Shape) : s.mask.count true = s.denseVolume := by
  simp [Shape.mask, Shape.axes, Shape.denseVolume, Nat.mul_assoc]

end BinaryHalo

end NearSquareRoot
end Computability
end OAI
