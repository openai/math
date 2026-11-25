import OAI.Computability.MultitapeWeakETH.CallProgram

/-! # Equality of bounded physical calls and the native RAM interpreter -/

namespace OAI.Computability.MultitapeWeakETH.CallProgram

open IntegerMultiplication Code VPVNP RAMTape BurstRAM PrivateRAM NativeGrid
open private advance from OAI.Computability.MultitapeWeakETH.CallProgram
noncomputable section

variable {p r k w : ℕ}

abbrev Stores (w : ℕ) := List (Word w × Word w)

/-- Replay requires only the terminal write log. Reads and ticks have no
effect on the external memory. -/
def storeEvents (log : Stores w) (events : List (Event w)) : Stores w :=
  events.foldl (fun ls e => match e with | .write a v => (a,v)::ls | _ => ls) log

theorem memory_storeEvents (base : Memory w) (log : Stores w) (es : List (Event w)) :
    memory base (storeEvents log es) = after (memory base log) es := by
  induction es generalizing log with
  | nil => rfl
  | cons e es ih => cases e <;> apply ih

def result : Model w p r → Option (Option (Word w) × Stores w)
  | .finished v log => some (v,log)
  | _ => none

variable (T : Template p r k) (pub : Fin k → Word w) (base : Memory w)

private theorem fixed {x : Model w p r} (h : modelStep T pub base x = x) (j : ℕ) :
    (modelStep T pub base)^[j] x = x := Function.iterate_fixed h j

/-- Running out of fuel, supplying too few or too many choice bits, and a
rejecting instruction all give the same rejection as native execution. -/
theorem result_iterate (fuel : ℕ) (c : LogConfig w p r) (bits : Bits.Word) (log : Stores w) :
    result ((modelStep T pub base)^[fuel] (.running c bits log)) =
      (execute (T.instantiate w pub).program fuel c.denote (memory base log) bits).map
        (fun rep => (rep.result,storeEvents log rep.events)) := by
  induction fuel generalizing c bits log with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply,execute,← Machine.logProgram_step]
    simp only [modelStep]
    cases h : (T.instantiate w pub).logProgram.step c with
    | localStep next =>
      simp only [advance,CallAction.mapState,ih,Option.map_map]
      rfl
    | branch next =>
      cases bits with
      | nil => simp only [advance,CallAction.mapState,fixed T pub base (x:=.failed) rfl,result,Option.map_none]
      | cons b bs =>
        simp only [advance,CallAction.mapState,ih,Option.map_map]
        rfl
    | read a next =>
      simp only [advance,CallAction.mapState,ih,Option.map_map]
      rfl
    | write a v next =>
      simp only [advance,CallAction.mapState,ih,Option.map_map]
      rfl
    | finish res =>
      cases bits <;> simp [advance,CallAction.mapState,fixed T pub base (x:=.failed) rfl,
        fixed T pub base (x:=.finished res log) rfl,result,storeEvents]
    | reject => simp [advance,CallAction.mapState,fixed T pub base (x:=.failed) rfl,result]

/-- Iterating the compiled opcode and callback on the exposed tape fields has
the same terminal configuration as the ghost evaluation. -/
theorem tick_iterate (read : Read) (grid : Tally)
    (rd : ∀ log (a : Word w), read ((grid,wordBits a),writes log) = wordBits (memory base log a.val))
    (x : Model w p r) (j : ℕ) :
    (fun st => tick T read (grid,st))^[j] (encode pub x) =
      encode pub ((modelStep T pub base)^[j] x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply,tick_spec T pub read grid base rd,ih]

end
end OAI.Computability.MultitapeWeakETH.CallProgram
