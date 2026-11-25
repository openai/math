import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotPreparation
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotCost

/-! # Common fences for the physical tally passes and the prepared trial -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotLayout
open IntegerMultiplication TM
variable {A Q I : Type} [DecidableEq I]
variable (start : Q) (input : I → Tape A) (idx : I) (blank mark : A) (lit : PublishedAttempt.Symbol A)
    (lo hi : I → ℤ)
local notation "F" => frame start input idx blank mark lit lo hi

theorem raw_origins (inputOrigin : ∀ j, (input j).pos=0) (i : ℕ) (j : I) :
    ((raw start input idx blank mark i).tape j).pos=0 := by
  simp only [raw]
  split <;> simp [inputOrigin]

theorem published_origins (inputOrigin : ∀ j, (input j).pos=0) (i a : ℕ) (j : Bank I) :
    ((published start input idx blank mark lit lo hi i a).tape j).pos=0 := by
  obtain _ | (j|b) := j
  · rfl
  · exact raw_origins start input idx blank mark inputOrigin i j
  · rfl

theorem frame_pos (inputOrigin : ∀ j, (input j).pos=0) (i a u v : ℕ) (j : Axis I) :
    0 ≤ (F i a u v j).pos ∧ (F i a u v j).pos ≤ (i+a : ℕ) := by
  cases j with
  | inl b =>
    rw [cursor_eq]
    cases b <;> simp [SlotTracks.tape,RoundExpose.cursor,RoundControl.cursor]
  | inr j =>
    have h := published_origins start input idx blank mark lit lo hi inputOrigin u v j
    change 0 ≤ ((published start input idx blank mark lit lo hi u v).tape j).pos ∧ _
    change _ ∧ ((published start input idx blank mark lit lo hi u v).tape j).pos ≤ (i+a : ℕ)
    simp [h]
    omega

theorem tally_fenced {P : Type} (m : Rule (Letter A) P (Axis I)) (inputOrigin : ∀ j, (input j).pos=0)
    (i a u v : ℕ) {s y R} (run : Trace (advance m) ⟨s,F i a u v⟩ (2*(i+a)+5) y)
    (room : 3*(i+a)+5 ≤ R) :
    FencedRun m (fun _ => -(R : ℤ)) (fun _ => R) ⟨s,F i a u v⟩ (2*(i+a)+5) y := by
  apply fencedRun_of_call_clock run _ le_rfl
  intro j
  obtain ⟨h1,h2⟩ := frame_pos start input idx blank mark lit lo hi inputOrigin i a u v j
  dsimp
  omega

end Uniform.SlotLayout

end NearSquareRoot
end Computability
end OAI
