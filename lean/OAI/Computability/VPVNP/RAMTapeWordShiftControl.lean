import OAI.Computability.VPVNP.RAMTapeStacks
import OAI.Computability.VPVNP.RAMTapeWord
import Mathlib.Tactic.DeriveFintype

/-!
# Finite control for a bounded variable shift

The loop removes a bit from the data and tries to subtract one from the shift
amount. Each successful subtraction fills a vacated slot with zero. If the
amount is zero, the machine puts the current bit back and copies the remaining
data to the output. If the data runs out, it discards the unused amount.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.Shift

open RAMTape

/-- Stacks for the remaining shift amount, data word, reversed temporary data, output and
scratch bits. -/
inductive Reg
  | amount | data | temp | output | scratch
  deriving DecidableEq

instance : Fintype Reg :=
  ⟨{.amount, .data, .temp, .output, .scratch}, fun k => by cases k <;> simp⟩

/-- Control for the bounded shift loop, decrementing the amount, inserting zeros, and reversing
data when implementing a left shift. -/
inductive State
  | start | prepare | putPrepare (b : Bool)
  | loop | borrow (b : Bool) | borrowFalse (b : Bool) | borrowOne
  | restore | putTrue | clear (b : Bool) | zero (b : Bool) | consume | discard
  | reverseData | putTemp (b : Bool) | restoreData | putOut (b : Bool)
  | finish | reverseOut | putFinal (b : Bool) | done
  deriving DecidableEq, Fintype

/-- Fixed control that discards at most one data bit per successful decrement and preserves the
word width by filling vacated positions with zeros. -/
def code (left : Bool) : StackCode Reg State
  | .start => .goto (if left then .prepare else .loop)
  | .prepare => .pop .temp fun b => b.elim .loop .putPrepare
  | .putPrepare b => .push .data b .prepare
  | .loop => .pop .data fun b => b.elim .discard .borrow
  | .borrow b => .pop .amount fun a => a.elim (.clear b) fun v =>
      if v then .borrowOne else .borrowFalse b
  | .borrowFalse b => .push .scratch true (.borrow b)
  | .borrowOne => .push .amount false .restore
  | .restore => .pop .scratch fun t => t.elim .consume (fun _ => .putTrue)
  | .putTrue => .push .amount true .restore
  | .clear b => .pop .scratch fun t => t.elim (.zero b) (fun _ => .clear b)
  | .zero b => .push .data b .reverseData
  | .consume => .push .output false .loop
  | .discard => .pop .amount fun a => a.elim .finish (fun _ => .discard)
  | .reverseData => .pop .data fun b => b.elim .restoreData .putTemp
  | .putTemp b => .push .temp b .reverseData
  | .restoreData => .pop .temp fun b => b.elim .finish .putOut
  | .putOut b => .push .output b .restoreData
  | .finish => .goto (if left then .reverseOut else .done)
  | .reverseOut => .pop .output fun b => b.elim .done .putFinal
  | .putFinal b => .push .temp b .reverseOut
  | .done => .halt true

/-- Place the five supplied lists on the shift amount, data, temporary, output and scratch
ports. -/
def store (amount data temp output scratch : List Bool) : Stacks Reg
  | .amount => amount
  | .data => data
  | .temp => temp
  | .output => output
  | .scratch => scratch

theorem update_store (a d t o s bits : List Bool) (k : Reg) :
    Function.update (store a d t o s) k bits = match k with
      | .amount => store bits d t o s
      | .data => store a bits t o s
      | .temp => store a d bits o s
      | .output => store a d t bits s
      | .scratch => store a d t o bits := by
  funext i
  cases k <;> cases i <;> simp [store]

end TapeWord.Shift

end VPVNP
end Computability
end OAI
