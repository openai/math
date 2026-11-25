import OAI.Hierarchy.TaggedPhysicalAssembly
import OAI.Hierarchy.TaggedScheduledPass
import OAI.Hierarchy.TaggedPassEval

namespace OAI
/-! # Evaluation and cost of the physical packed radix schedule -/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork RadixStage CatalystSubstitution
open scoped Classical
noncomputable section

variable {F : Type*} [Field F] {k : ℕ} {a B : ℝ}

/-- Install the full six-stage evaluation law in every meaningful slot of the
native, bounded-size sequence. -/
theorem stage_run {h n : ℕ} (two : 2 ≤ h) (g : GridScales a B h) (count : n+1 ≤ 2^(passBits h))
    (cover : h+1 ≤ (n+1)*digitBits a h) (Y : ∀ i,(passFormatAt a B h n i (2*h+4)).Calls F k) :
    ∃ S : StageRun h n Y,S.Room 6000000000000 := by
  apply assemble_stage_run two g count cover Y
  intro i hi
  apply scheduled_computes F i hi
  let d := digitBits a h
  let j := packBits B h
  have room : j+2 ≤ d := by have := g.digit_room; dsimp [d,j]; omega
  have step := (rawShape h d j i).computes (RadixRecord.blank h) (RadixRecord.real h) (RadixRecord.dummy h)
    (RadixRecord.digit h d i) F room (blank_real h) (by simp [blank_dummy,blank_real])
  exact fun x hx y => step x (flags_allowed x hx) y

end
end Hierarchy.Tagged.Radix

end OAI
