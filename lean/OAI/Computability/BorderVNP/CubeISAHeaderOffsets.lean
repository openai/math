import OAI.Computability.BorderVNP.CubeISALengthImage

/-! # Compact offsets of the cube declaration in the common header

The coordinate word comes first. The remaining words visit sorted symbol
pairs in row-major order with candidate cuts varying fastest. The native
dense row table includes a zero lower triangle, but this triangle consumes
no input bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.DeclarationBits

open RoutingISA.CubeLengths

/-- Whether dense row-major field `k` belongs to the unordered-pair triangle. -/
def upper (d a k : ℕ) : Prop := k/a/d ≤ k/a%d

instance (d a k : ℕ) : Decidable (upper d a k) := inferInstanceAs (Decidable (_ ≤ _ : Prop))

/-- The number of actual declaration fields preceding the dense table cursor. -/
def fieldsBefore (d a : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => fieldsBefore d a k + (decide (upper d a k)).toNat

/-- Address of the next actual field at this dense cursor. -/
def fieldStart (source d a cw rw k : ℕ) : ℕ := source+cw+fieldsBefore d a k*rw

/-- Division and remainder in the native loop test exactly the ordered pair
used by the square table's finite enumeration. -/
theorem upper_iff {d a : ℕ} (k : Fin (d*d*a)) :
    upper d a k.val ↔ ((entryOrder d a).symm k).1.1 ≤ ((entryOrder d a).symm k).1.2 := Iff.rfl

end Cube.DeclarationBits

end BorderVNP
end Computability
end OAI
