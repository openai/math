import OAI.Hierarchy.DescentResetOperandSlices
import OAI.Hierarchy.DescentNextSignedWindow

namespace OAI
/-! # Recovering the installed child cable at its actual rendered reset position -/
namespace Hierarchy.DescentResetOperandSlices
open DescentSIMDLookup DescentNextSignedWindow DescentOperandStateBanks
open scoped Classical Fin.CommRing
noncomputable section
variable {b : ℕ}

/-- The stored two-field correction recovers exactly the first cable serial
in the measured window and the index inside that particular emitted child. -/
theorem from_render {degree cap : ℕ} (role : Role) (tag : Cell b) (hub : Cell 1)
    (unit : ℕ) (_positive : 0<unit) (chunk : Cell b) (r : Record degree cap)
    (live : DescentSharedCableNames.Stage.Live degree cap)
    (kind : tag.val=1)
    (useRole : marked role (decide (hub.val=1))=r.marked ∨ chunk.val<unit)
    (hit : render r (chunk.val/unit)=some live) :
    r.shared+(part unit true (mode role tag hub) chunk).val=live.wire.val-live.within.val ∧
    (part unit false (mode role tag hub) chunk).val=
      (if r.marked then chunk.val%unit else chunk.val) := by
  have hd : chunk.val/unit<2^b:=(Nat.div_le_self ..).trans_lt chunk.isLt
  have hm : chunk.val%unit<2^b:=(Nat.mod_le ..).trans_lt chunk.isLt
  have parts : live.wire.val=r.shared+chunk.val/unit ∧
      live.within.val=(if r.marked then 0 else chunk.val/unit) := by
    simp [render] at hit
    obtain ⟨_, rfl⟩ := hit
    exact ⟨rfl, rfl⟩
  rw [parts.1,parts.2,case_mode role tag hub kind]
  by_cases splitAt : marked role (decide (hub.val=1))=true
  · simp only [splitAt,ite_true]
    rw [(two_part unit chunk).1,(two_part unit chunk).2,Fin.val_cast_of_lt hd,Fin.val_cast_of_lt hm]
    rcases useRole with h|h
    · rw [←h,splitAt];simp
    · simp [Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h]
  · simp only [ite_eq_right splitAt]
    rw [(one_part unit chunk).1,(one_part unit chunk).2]
    rcases useRole with h|h
    · have : r.marked=false:=by cases m:r.marked <;> simp_all
      simp [this]
    · simp [Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h]

end
end Hierarchy.DescentResetOperandSlices

end OAI
