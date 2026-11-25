import OAI.Computability.NearSquareRoot.InterchangeROMFamily
import OAI.Computability.NearSquareRoot.InterchangeROMStageSelect

/-! # Sizes of the center bank selected by the effective atlas search -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFamily

open Interchange InterchangeROMRepair InterchangeAddress

theorem bank_width (x : Template.Data) : x.labels * Raw.rowCount x.m = x.width := by
  unfold Template.Data.width Raw.rowCount TemplateCost.width
  ac_rfl

theorem legal_width {j t : ℕ} {x : Template.Data} (h : Template.Data.Valid j t x) :
    3 ≤ x.labels * Raw.rowCount x.m ∧ x.labels * Raw.rowCount x.m ≤ x.b := by
  obtain ⟨_,_,_,_,less,hm,labels,_,_⟩ := h.1
  have leading : 3 ≤ 2^x.m := (by decide : 3 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) hm)
  have order : 0 < (Sizes.pencilOrder x.m)^(Sizes.clockDigits x.m) := by
    unfold Sizes.pencilOrder
    positivity
  have basis : 0 < Sizes.basisCount x.m := by unfold Sizes.basisCount; positivity
  exact ⟨(((leading.trans (Nat.le_mul_of_pos_right _ order)).trans
    (Nat.le_mul_of_pos_right _ basis)).trans (Nat.le_mul_of_pos_left _ labels)),
    (bank_width x).le.trans less.le⟩

theorem modulus {j t : ℕ} {x : Template.Data} (h : Template.Data.Valid j t x) :
    x.modulusIndex + 1 = x.p := by
  have odd := h.1.2.1
  unfold Template.Data.modulusIndex
  omega

end InterchangeROMFamily

end NearSquareRoot
end Computability
end OAI
