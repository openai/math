import OAI.Hierarchy.DescentDonorLaneNumbers
import OAI.Hierarchy.DescentPrivateDepotPort
import OAI.Hierarchy.DescentDonorFreshRAM

namespace OAI
/-! # Per-lane charge of the physically read topology and eight new widths -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Fresh
open DescentSIMDLookup DescentPacking.PackedMatch DescentPacking.PackedMatch.Local
variable (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape)

theorem code_page (payload amount : ℕ) (coverage : laneWidth s z≤amount) :
    let M:=lanes payload amount
    (M+1)*codeSize s z M≤2^(payload/2) := by
  intro M
  have room : M*laneWidth s z≤payload/2 :=
    (Nat.mul_le_mul_left M coverage).trans (lanes_fit payload amount)
  have slack : M+1≤2^M := Nat.lt_two_pow_self
  have exp : M+(rawBits s*M+SixBirths.topology z M+SixBirths.width z M)=M*laneWidth s z := by
    unfold laneWidth SixBirths.topology SixBirths.width
    ring
  calc
    _ ≤ 2^M*codeSize s z M := Nat.mul_le_mul_right _ slack
    _ = 2^(M*laneWidth s z) := by rw [codeSize,←pow_add,exp]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) room

/-- Every leaf speaks the same bounded row language. -/
theorem all_pages (payload amount leaves : ℕ) (coverage : laneWidth s z≤amount) :
    let M:=lanes payload amount
    leaves*((M+1)*codeSize s z M)≤leaves*2^(payload/2) :=
  Nat.mul_le_mul_left _ (code_page s z payload amount coverage)

end Hierarchy.DescentRawCablePanel.DepotRAM.Fresh

end OAI
