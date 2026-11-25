import OAI.Hierarchy.TaggedSliceFeasible
import OAI.Hierarchy.TaggedNarrowAllowance

namespace OAI
/-! # The base strip of the induction on address length -/

noncomputable section
namespace Hierarchy.Tagged
open Filter Real

/-- A feasible width-one estimate with a strict margin at the initial point
pays the full uniform allowance on a positive-width strip. -/
theorem bounded_narrow_strip {F : Type*} [Field F] {k : ℕ} {s r : ℝ} {u : ℝ → ℝ}
    (hu : TaggedWidthProfile.Admissible s u) (base : Feasible F k 1 r) (margin : r < u 1) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ D : ℝ, C < D →
      ∀ᶠ h : ℕ in atTop, ∀ w : ℕ, h ≤ w → logb h w ≤ 1+κ → Bounded F k h w u 1 D := by
  obtain ⟨κ,pos,allow⟩ := narrow_allowance hu margin
  obtain ⟨A,C,_,hC,formats⟩ := Slices.eventually_from_feasible base
  refine ⟨κ,C,pos,hC,fun D large => ?_⟩
  filter_upwards [formats D (1+κ) large (by linarith),allow A] with h ok cost
  intro w wide narrow
  obtain ⟨cap,bill⟩ := cost w wide narrow
  obtain ⟨Y,size,gap⟩ := ok w (by simpa using wide) cap
  exact ⟨Y,by simpa only [one_mul] using size.trans bill,gap⟩

end Hierarchy.Tagged

end
end OAI
