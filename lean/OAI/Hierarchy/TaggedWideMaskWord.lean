import OAI.Hierarchy.TaggedWideSwitchTariff
import OAI.Hierarchy.TaggedWideWidthRoom

namespace OAI
/-! # Eventual word widths for the actual paid mask and history columns -/

namespace Hierarchy.Tagged.WideParent
open ProbeStage ProbeStage.Native Filter

theorem columnBits_le_height {κ A : ℝ} (K : ℕ) :
    ∀ᶠ x : WideParent κ A in large κ A,columnBits (K*x.w)≤ x.h+1 := by
  filter_upwards [fixed_mul_width (κ:=κ) (A:=A) K] with x small
  have depth : Nat.log 2 (K*x.w+1)≤ x.h:=by
    simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) small
  exact Nat.succ_le_succ depth

theorem columnBits_wordBits {κ A : ℝ} (K : ℕ) :
    ∀ᶠ x : WideParent κ A in large κ A,∀ d copies : ℕ,columnBits (K*x.w)≤ wordBits x.h d copies := by
  filter_upwards [columnBits_le_height (κ:=κ) (A:=A) K] with x room
  intro d copies
  rw [wordBits_linear]
  omega

end Hierarchy.Tagged.WideParent

end OAI
