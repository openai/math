import OAI.Computability.NearSquareRoot.ScheduleStagingOffer
import OAI.Computability.NearSquareRoot.ScheduleStagingControl

/-!
# Controller representations of the public digit ports

The controller's tree-node letter serves as the temporary sentinel. Its bit
and separator letters store the digit query directly. A returned public bit
stream is already the raw stack expected by the collection phase.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingLetters

open IntegerMultiplication TM Code Bits
open CommonAlphabet CommonAlphabet.Pipeline StagingPorts
open ChunkControl (Driver)
open ChunkTask (Input)
open ChunkLoop (Operands)
open ChunkPhases (digitQuery)

variable (d : Driver)

private def embed : Public.Letter → StagingControl.Letter d
  | none => none
  | some none => some (.inl .sep)
  | some (some b) => some (.inl (.bit b))

private def read : StagingControl.Letter d → Public.Letter
  | some (.inl .sep) => Public.sep
  | some (.inl (.bit b)) => Public.bit b
  | _ => none

def encoding : Encoding (StagingControl.Letter d) where
  embed := embed d
  read := read d
  decode := by rintro (_|(_|b)) <;> rfl

@[simp] theorem embed_blank : (encoding d).embed none = none := rfl
@[simp] theorem embed_sep : (encoding d).embed Public.sep = some (.inl .sep) := rfl
@[simp] theorem embed_bit (b : Bool) : (encoding d).embed (Public.bit b) = some (.inl (.bit b)) := rfl

def sentinel : StagingControl.Letter d := some (.inl .node)

theorem reserved : ∀ a, sentinel d ≠ (encoding d).embed a := by
  rintro (_|(_|b)) h <;> cases h

private theorem display_tape {A : Type} (s : List A) :
    StagingControl.tape 0 s = StagingCopy.atPos none (-(s.length : ℤ)) (s.map some) := by
  change Tape.mk _ _ = Tape.mk _ _
  rw [Tape.mk.injEq]
  exact ⟨zero_sub _,(SM.display_loaded s).symm⟩

private theorem request_word (x y : Word) :
    (((StagingPhases.request (x,y)).map (Sum.inl (β:=Prog.Ptr (ChunkDispatch.area (StagingOpen.cmd d))))).map some) =
      (rawWord x y).map (encoding d).embed := by
  simp [StagingPhases.request,rawWord,List.map_map,Function.comp_def]

/-- The actual staged register contains the public input word at the top address
specified by the offer machine. -/
theorem query (B : StagingControl.Axis d → ℤ) (hB : B (StagingOpen.one d) = 0)
    (m : Operands → Word) (p : Input) (t : ℕ) :
    (StagingControl.entry d B .digit
      (StagingPhases.slot (p.bundle m t) (StagingPhases.request (digitQuery m p t)))).tape
        (StagingOpen.one d) =
    StagingOffer.queryTape (encoding d) p.u (digitQuery m p t).1 (digitQuery m p t).2 := by
  have width := p.query_width m t
  change (digitQuery m p t).1.length = p.u ∧ (digitQuery m p t).2.length = p.u at width
  rw [StagingControl.one_tape,hB,display_tape,StagingOffer.queryTape,StagingOffer.encoded_word,
    embed_blank,request_word]
  congr 1
  simp [StagingPhases.request,width.1,width.2]
  omega

/-- The public output tape equals the collection phase's register, including
its physical head coordinate and its infinite blank exterior. -/
theorem reply (B : StagingControl.Axis d → ℤ) (hB : B (StagingOpen.one d) = 0)
    (m : Operands → Word) (p : Input) (t : ℕ) (ans : Word) (hans : ans.length = 2*p.u) :
    (StagingControl.entry d B .collect (StagingPhases.slot (p.bundle m t) (ans.map Ltr.bit))).tape =
    Function.update
      (StagingControl.entry d B .digit
        (StagingPhases.slot (p.bundle m t) (StagingPhases.request (digitQuery m p t)))).tape
      (StagingOpen.one d)
      (imageTape (encoding d).embed (-(2*p.u : ℤ)) (Tape.loaded none (ans.map Public.bit))) := by
  rw [StagingControl.replace_reply d B (p.bundle m t) (StagingPhases.request (digitQuery m p t)),
    hB,display_tape,image_loaded]
  congr 1
  change Tape.mk _ _ = Tape.mk _ _
  rw [Tape.mk.injEq]
  constructor
  · simp [hans]
  · simp [List.map_map,Function.comp_def]

end StagingLetters

end NearSquareRoot
end Computability
end OAI
