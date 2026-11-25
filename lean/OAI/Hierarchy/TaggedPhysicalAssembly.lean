import OAI.Hierarchy.TaggedPassHistory
import OAI.Hierarchy.TaggedPassSockets
import OAI.Hierarchy.TaggedRadixTerminal
import OAI.Hierarchy.TaggedScheduledPass
import OAI.Hierarchy.TaggedPassRunCore

namespace OAI
/-! # The physical sequence of bounded-digit stable radix passes -/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork RadixStage CatalystSubstitution
open Filter
open scoped Classical
noncomputable section

variable {F : Type*} [Field F] {k : ℕ} {a B : ℝ}

/-- Passes past the last scheduled pass have no cells. The meaningful stages
are precisely the physical three-call packed digit networks. -/
theorem assemble_stage_run {h n : ℕ} (two : 2 ≤ h) (g : GridScales a B h) (count : n+1 ≤ 2^(passBits h))
    (cover : h+1 ≤ (n+1)*digitBits a h) (Y : ∀ i,(passFormatAt a B h n i (2*h+4)).Calls F k)
    (eval : ∀ i, i ≤ n → ComputesOn (scheduledNetwork F a B h n i)
      (PassShape.weight F (passShapeAt a B h n i) (RadixRecord.width h))
      allowed (rawRun h (digitBits a h) (packBits B h) i)) :
    ∃ S : StageRun h n Y,S.Room 6000000000000 := by
  let d := digitBits a h
  let j := packBits B h
  let w := RadixRecord.width h
  let shape (i : ℕ) := passShapeAt a B h n i
  let A := state h d j
  let H (i : ℕ) := (shape i).PassHoles w
  let run := rawRun h d j
  let good (i : ℕ) (x : A i → Bool) := allowed x
  have room : j+2 ≤ d := by have := g.digit_room; dsimp [d,j]; omega
  let attach (i : ℕ) := (shape i).attached w room (Y i)
  let coords (i : ℕ) : H i ≃ Sockets (Y i).occurrences := Classical.choose (attach i)
  have coordWt i z : exactWeight (Y i).occurrences (z ∘ (coords i).symm) = PassShape.weight F (shape i) w z :=
    Classical.choose_spec (attach i) z
  let stage := scheduledNetwork F a B h n
  have computes (i : ℕ) (hi : i ≤ n) : ComputesOn (stage i)
      (fun z => exactWeight (Y i).occurrences (z ∘ (coords i).symm)) (good i) (run i) := by
    simp only [coordWt]
    exact eval i hi
  let S : StageRun h n Y := {
    state := A
    holes := H
    stage := stage
    sockets := coords
    run := run
    reachable := good
    computes := computes
    keep := fun i _ _ => allowed_next room i _
    feed := RadixRecord.feed h
    start := RadixRecord.canonical_feed
    scan := RadixRecord.scan F (slotSequence (2^(h+1)) d j (n+1)) h
    finish := fun x => RadixRecord.scan_finish F (by omega) x _ (final_order room n cover x).1 (final_order room n cover x).2 }
  refine ⟨S,⟨?_,?_⟩⟩
  · intro i hi
    exact scheduled_cost F two g count i hi
  · have vol := (slotSequence_bounds count g.digit_room (Nat.le_succ_of_le g.last_room) (n+1) le_rfl).2
    exact (RadixRecord.scan_room F vol).trans (Nat.mul_le_mul_right _ (by decide : 132003 ≤ 6000000000000))

end
end Hierarchy.Tagged.Radix

end OAI
