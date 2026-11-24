import OAI.Computability.VPVNP.TallyConstants
import OAI.Computability.VPVNP.RAMLayout
import Mathlib.Tactic.DeriveFintype

/-! # Computing the incident-vector width on the validator's actual stacks

The address and bucket registers contain `d` and `H` in unary. The fixed program
forms `w = (d+10)^4`, counts the sorting layers, and writes the entire incident
width of equation (10.1). It returns both input registers and clears its scratch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputWidth

open Tally

/-- Unary counters for the address, bucket, incident width, and intermediate arithmetic in the
layout-width calculation. -/
inductive Port where
  | address | bucket | incident | base | duplicate | square | word | layers
  | blocks | payload | factor | outer | tmp
  deriving DecidableEq

noncomputable instance : Fintype Port := derive_fintype% Port

/-- Start width computation with address width and bucket size on their counters and zero
elsewhere. -/
def initial (d H : ℕ) : State Port
  | .address => d
  | .bucket => H
  | _ => 0

/-- Final width state containing the original address and bucket tallies and the complete
incident-vector width. -/
def result (d H : ℕ) : State Port :=
  Function.update (initial d H) .incident (RAMLayout.width d H ((d+10)^4))

/-- Two squarings of `d+10`. Each multiply reads disjoint input stacks. -/
def wordProgram : Program Port :=
  (Program.copy .address .base .tmp (by decide) (by decide) (by decide)).seq <|
  (Program.addConst .base 10).seq <|
  (Program.copy .base .duplicate .tmp (by decide) (by decide) (by decide)).seq <|
  (Program.mul .base .duplicate .square .outer .tmp (by decide)).seq <|
  (Program.clear .duplicate).seq <|
  (Program.copy .square .duplicate .tmp (by decide) (by decide) (by decide)).seq <|
  (Program.mul .square .duplicate .word .outer .tmp (by decide)).seq <|
  Program.clear .duplicate

/-- Intermediate tallies for the address width plus ten, its square, and its fourth power,
which gives the word width. -/
def words (d H : ℕ) : State Port
  | .base => d+10
  | .square => (d+10)^2
  | .word => (d+10)^4
  | p => initial d H p

/-- Count `(d+1).choose 2` sorting layers and multiply by bucket and word widths. -/
def payloadProgram : Program Port :=
  (Program.triangle .address .layers .outer .tmp (by decide) (by decide) (by decide)
    (by decide) (by decide)).seq <|
  (Program.mul .bucket .layers .blocks .outer .tmp (by decide)).seq <|
  Program.mul .word .blocks .payload .outer .tmp (by decide)

/-- Intermediate counts for sorting layers, bucket slots across those layers, and their
word-width product. -/
def payloads (d H : ℕ) : State Port
  | .layers => (d+1).choose 2
  | .blocks => H*(d+1).choose 2
  | .payload => (d+10)^4*(H*(d+1).choose 2)
  | p => words d H p

/-- Add the successor-field width and the sorting-field width into the output register. -/
def countProgram : Program Port :=
  (Program.addConst .factor 16).seq <|
  (Program.mul .factor .word .incident .outer .tmp (by decide)).seq <|
  (Program.clear .factor).seq <|
  (Program.addConst .factor 40).seq <|
  (Program.mul .factor .payload .incident .outer .tmp (by decide)).seq <|
  Program.clear .factor

/-- State after writing the full incident width while the intermediate geometry tallies are
still present. -/
def counted (d H : ℕ) : State Port :=
  Function.update (payloads d H) .incident (RAMLayout.width d H ((d+10)^4))

/-- Erase the base, square, word, layers, blocks, and payload counters after storing the
incident width. -/
def cleanup : Program Port :=
  (Program.clear .base).seq <| (Program.clear .square).seq <| (Program.clear .word).seq <|
    (Program.clear .layers).seq <| (Program.clear .blocks).seq <| Program.clear .payload

/-- A single fixed finite control, independent of `d` and `H`. -/
def program : Program Port := wordProgram.seq (payloadProgram.seq (countProgram.seq cleanup))

private theorem eval_wordProgram (d H : ℕ) : wordProgram.eval (initial d H) = words d H := by
  funext p
  cases p <;> simp (config := { decide := true }) [wordProgram, initial, words] <;> ring

private theorem eval_payloadProgram (d H : ℕ) : payloadProgram.eval (words d H) = payloads d H := by
  funext p
  cases p <;> simp (config := { decide := true }) [payloadProgram, words, initial, payloads]

private theorem eval_countProgram (d H : ℕ) : countProgram.eval (payloads d H) = counted d H := by
  funext p
  cases p <;> simp (config := { decide := true }) [countProgram, counted, payloads, words, initial,
    RAMLayout.width_eq]
  ring

private theorem eval_cleanup (d H : ℕ) : cleanup.eval (counted d H) = result d H := by
  funext p
  cases p <;> simp (config := { decide := true }) [cleanup, result, counted, payloads, words, initial]

theorem eval_program (d H : ℕ) : program.eval (initial d H) = result d H := by
  change cleanup.eval (countProgram.eval (payloadProgram.eval (wordProgram.eval (initial d H)))) = _
  rw [eval_wordProgram, eval_payloadProgram, eval_countProgram, eval_cleanup]

theorem ready_program (d H : ℕ) : program.ready (initial d H) := by
  simp only [program, Program.seq_ready, eval_wordProgram, eval_payloadProgram, eval_countProgram]
  simp (config := { decide := true }) [wordProgram, payloadProgram, countProgram, cleanup,
    initial, words, payloads]

/-- The subroutines' exact instruction counts add across the four stages. -/
theorem work_program (d H : ℕ) : program.work (initial d H) =
    wordProgram.work (initial d H) + (payloadProgram.work (words d H) +
      (countProgram.work (payloads d H) + cleanup.work (counted d H))) := by
  simp only [program, Program.seq_work, eval_wordProgram, eval_payloadProgram, eval_countProgram]

theorem runs (d H : ℕ) : program.code.Runs (program.work (initial d H))
    (encode (initial d H)) (encode (result d H)) :=
  eval_program d H ▸ program.spec (initial d H) (ready_program d H)

end RAMTape.InputWidth

end VPVNP
end Computability
end OAI
