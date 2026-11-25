import OAI.Hierarchy.DescentRegisterTimelineCore
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # One word width for every floor of the actual register timeline -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook Filter
noncomputable section

variable {ι : ℕ→Type*} {w : ℕ→ℕ} (dates : ∀h,ι h→ℕ)
    {Cut : ∀h,ι h→ℕ→Type*}
    (issue : ∀h (i:ι h) j,Cut h i j→Position→Move (w h)→Prop)
    (initial : ∀h,ι h→Position)
local notation "pos_" => (fun h i=>position (issue h i) (initial h i))

/-- A valid invocation is billed at its actual entry. The fallback in the
definition of the selector has zero address increment. -/
theorem span_of_issued {h j bound : ℕ} {i : ι h}
    (paid : ∀(c:Cut h i j) (move:Move (w h)),issue h i j c (pos_ h i j) move →
      move.next.floor-(pos_ h i j).floor≤bound) :
    span (issue h i) (initial h i) j≤bound :=by
  change (selected (issue h i) j (pos_ h i j)).next.floor-(pos_ h i j).floor≤bound
  unfold selected
  split
  · rename_i found
    obtain ⟨c,hit⟩:=found.choose_spec.1
    exact paid c _ hit
  · simp

/-- Includes every prefix and the complete physical end even when the number
of stages, original input size, and all dated pointers depend on the height. -/
theorem public_floors
    (header : Bounded (fun h i=>(initial h i).floor)) (count : Bounded dates)
    (charged : ∃E:ℕ,∀ᶠ h:ℕ in atTop,∀(i:ι h) (j:Fin (dates h i))
      (c:Cut h i j) (move:Move (w h)),issue h i j c (pos_ h i j) move →
      move.next.floor-(pos_ h i j).floor≤2^(E*h)) :
    ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀(i:ι h) (j:ℕ),j≤dates h i → (pos_ h i j).floor<2^(K*h) :=by
  obtain ⟨B,heads⟩:=header
  obtain ⟨A,stages⟩:=count
  obtain ⟨E,visited⟩:=charged
  refine ⟨A+max B E+2,?_⟩
  filter_upwards [heads,stages,visited,eventually_ge_atTop 1] with h hh hs hv hp
  intro i j limit
  rw [position_floor]
  apply within_word (A:=A) (B:=max B E) hp
  · exact (hh i).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h (le_max_left ..)))
  · exact limit.trans (hs i)
  · intro k earlier
    exact (span_of_issued issue initial (hv i ⟨k,lt_of_lt_of_le earlier limit⟩)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h (le_max_right ..)))

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
