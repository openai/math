import OAI.Hierarchy.DescentSignedTableDimensions

namespace OAI
/-! # The installed successor-neighbor book reserves an entry for every path -/
namespace Hierarchy.DescentPackedChildNeighbor.SIMD.ROM
theorem paths_le_cells (P a b M H G : ℕ) : P≤cells P a b M H G :=by
  have keep : P≤P*2^(a*M+b):=Nat.le_mul_of_pos_right P (Nat.two_pow_pos _)
  exact keep.trans ((Nat.le_add_right _ _).trans (Nat.le_add_left _ _))
end Hierarchy.DescentPackedChildNeighbor.SIMD.ROM

end OAI
