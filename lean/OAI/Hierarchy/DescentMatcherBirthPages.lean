import OAI.Hierarchy.DescentPackedSixBirthTables
import OAI.Hierarchy.DescentPackedSixBirths

namespace OAI
/-! # Exact two-page budget for the published six-birth matcher table -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

/-- Count both six-party lookup pages and all literal branches of the output width. -/
theorem birth_pages (s : Shape) (h u M V : ℕ) (width : SixBirths.unit s≤u)
    (packed : u*M≤h/2) (page : 2^(h/2)≤V) :
    SixBirths.entries s M≤2*V ∧ 2^(SixBirths.width s M)≤V := by
  have cpu : SixBirths.profiles s M+SixBirths.topology s M≤h/2 := calc
    _ = (s.digit*s.pairs+s.outputBits)*M := by unfold SixBirths.profiles SixBirths.topology;ring
    _ ≤ u*M := Nat.mul_le_mul_right _ ((le_max_left ..).trans width)
    _ ≤ _ := packed
  have outWidth : SixBirths.width s M≤h/2 := calc
    _ = ((s.digit+1)*(s.pairs*6))*M := by unfold SixBirths.width;ring
    _ ≤ u*M := Nat.mul_le_mul_right _ ((le_max_right ..).trans width)
    _ ≤ _ := packed
  exact ⟨(SixBirths.mount_size s M h cpu).trans (Nat.mul_le_mul_left 2 page),
    (Nat.pow_le_pow_right (by decide : 0<2) outWidth).trans page⟩

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

end OAI
