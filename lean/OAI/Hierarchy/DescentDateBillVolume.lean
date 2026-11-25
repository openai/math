import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Physical bit volume of one ordinary date -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill
open DescentSIMDLookup
def words (H G h u : ℕ) := 1+2^(h/2)+H+H*chunks G (lanes h u)
def volumeBits (H G h u : ℕ) := h+H*h+4*H*G*u+2^(h/2)*h

theorem words_bits (H G h u : ℕ) (pos : 0 < u) (wide : 2*u ≤ h) :
    words H G h u*h ≤ 2*volumeBits H G h u := by
  have measured:=volume H G h u pos wide
  unfold words volumeBits
  simp only [Nat.add_mul,Nat.one_mul]
  omega

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

end OAI
