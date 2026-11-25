import OAI.Computability.BorderVNP.CellFragmentWords
import OAI.Computability.BorderVNP.RoutingISACompactMachine

/-! # Private initialization of the external values from a typed sparse packet

The actual external bits are kept in a private stack during translation of the
metadata. A fixed linear sweep prepares deterministic literal instructions for
the interpreter without transmitting those instructions on the burst.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactPacket

open CellMacro CellMacro.Generator VPVNP.RAMTape

/-- One additional private stack holds the typed packet and then the reversed boundary bits. -/
abbrev Port := IO ⊕ Unit

/-- State of the four exposed stacks during private packet preparation. -/
def bank (r e o spare : List Bool) : Stacks Port := Sum.elim (io r e o) (fun _ => spare)

/-- The bit stack decoded by the input loader. -/
abbrev row : Port := .inl .row
/-- Lexical environment or temporarily the translated command list. -/
abbrev env : Port := .inl .env
/-- The reversed stream under construction. -/
abbrev out : Port := .inl .out
/-- Temporary stack privately reused after translation. -/
abbrev scratch : Port := .inr ()

private theorem updateSpare (r e o z v : List Bool) : Function.update (bank r e o z) scratch v =
    bank r e o v := by funext k; cases k <;> simp [scratch,bank]
private theorem updateOut (r e o z v : List Bool) : Function.update (bank r e o z) out v =
    bank r e v z := by
  funext k; cases k with
  | inr u => simp [out,bank]
  | inl j => cases j <;> simp [out,bank,io]

private def emitBit (b : Bool) := (Routine.push out false).followedBy (Routine.push out b)

/-- Emit the reverse binary stream for the remaining literal instructions, paying one pop
and two pushes per input bit. -/
def emitLiterals : FiniteRoutine Port := .ofRoutine
  (Routine.popLoop scratch (fun _ => true) (emitBit false) (emitBit true))

private theorem emitBit_run (b : Bool) (r e o z : List Bool) :
    (emitBit b).Runs 2 (bank r e o z) (bank r e (b::false::o) z) := by
  have h := Routine.runs_push out false (bank r e o z)
  rw [updateOut] at h
  have h' := Routine.runs_push out b (bank r e (false::o) z)
  rw [updateOut] at h'
  exact h.followedBy h'

private theorem emit_run (r e : List Bool) (z o : List Bool) :
    emitLiterals.Runs (3*z.length+1) (bank r e o z)
      (bank r e ((stream (z.map Op.literal)).reverse ++ o) []) := by
  induction z generalizing o with
  | nil => exact Routine.Runs.popLoop_empty scratch (fun _ => true) (emitBit false) (emitBit true) rfl
  | cons b z ih =>
    have h : (stream ((b::z).map Op.literal)).reverse ++ o =
        (stream (z.map Op.literal)).reverse ++ b::false::o := by
      simp [stream,Op.bits,List.append_assoc]
    rw [h,show 3*(b::z).length+1 = 1+2+(3*z.length+1) by simp; omega]
    apply Routine.Runs.popLoop_continue scratch (fun _ => true) (emitBit false) (emitBit true) (b := b) (hstack := rfl) (hrep := rfl) _ (ih _)
    rw [updateSpare]
    cases b <;> exact emitBit_run _ _ _ _ _

/-- Both source-order recovery and literal emission are local to the private machine. -/
def seed : Fragment Port := Fragment.plain
  ((VPVNP.EvaluatorRadixDivision.reverseOnto row scratch).followedBy emitLiterals)

/-- Seeding costs five private stack steps per real external bit plus two terminating pops. -/
theorem seed_run (ext description acc : List Bool) :
    seed.Runs (5*ext.length+2) (bank ext description acc [])
      (bank [] description ((stream (ext.reverse.map Op.literal)).reverse ++ acc) []) := by
  have rev := VPVNP.EvaluatorRadixDivision.reverseOnto_runs (src := row) (dst := scratch)
    (by decide) (bank ext description acc []) (bank [] description acc ext.reverse) rfl (by simp [bank,row,scratch,io])
    (by intro k a b; cases k with
        | inl j => cases j <;> simp_all [bank,row,io]
        | inr u => cases u; exact (b rfl).elim)
  have fill := emit_run [] description ext.reverse acc
  rw [List.length_reverse] at fill
  change (VPVNP.EvaluatorRadixDivision.reverseOnto row scratch).Runs (2*ext.length+1) _ _ at rev
  rw [show 5*ext.length+2 = (2*ext.length+1)+(3*ext.length+1) by omega]
  exact Fragment.runs_plain (rev.followedBy fill)

end RoutingISA.CompactPacket

end BorderVNP
end Computability
end OAI
