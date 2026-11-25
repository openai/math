import OAI.Computability.MultitapeWeakETH.CallClock
import OAI.Computability.VPVNP.RAMChain

/-! # Successive descriptor calls on one external write log -/

namespace OAI.Computability.MultitapeWeakETH.CallProgram

open IntegerMultiplication Code VPVNP RAMTape BurstRAM PrivateRAM NativeGrid StackInterpreter
open private live finish fail from OAI.Computability.MultitapeWeakETH.CallProgram
noncomputable section

variable {w p r k : ℕ} (T : Template p r k)

private def publicZero (k w : ℕ) : Fin k → Word w := fun _ => 0

def feed (bits : Bits.Word) : Model w p r → Model w p r
  | .finished (some v) log => .running ((T.instantiate w (publicZero k w)).logProgram.start v) bits log
  | _ => .failed

/-- The only legal source for a further call is a returned persistent word.
The old private bank is discarded, while all external writes are retained. -/
def feedBytes (q : Bits.Word × State p) : State p :=
  let s := q.2
  match s.1.1.val with
  | .returned => live T.entry (start T s.2.2).2 q.1 s.2.1.2
  | _ => fail

theorem feed_poly : Poly (feedBytes T) := by
  let f : Phase p → Bits.Word × State p → State p
    | .returned => fun q => live T.entry (start T q.2.2.2).2 q.1 q.2.2.1.2
    | _ => fun _ => fail
  have choose := select_poly (fun q : Bits.Word × State p => q.2.1.1)
    (Easy.snd.compose (Easy.fst.compose Easy.fst)).poly f (fun ph => ?_) (fun _ => fail) (Code.Poly.const _)
  · convert choose using 1
    funext q
    cases e : q.2.1.1.val <;> simp [feedBytes,e,f]
  · cases ph with
    | returned =>
      have fresh : Poly (fun q : Bits.Word × State p => (start T q.2.2.2).2) := ((Easy.snd.compose (Easy.snd.compose Easy.snd)).poly.compose (start_poly T)).sndCompose
      exact (((Code.Poly.const _).pair fresh).pair ((Easy.fst.poly.pair (by fun_prop)).pair (Code.Poly.const [])))
    | _ => exact Code.Poly.const _

theorem feed_spec (bits : Bits.Word) (x : Model w p r) :
    feedBytes T (bits,encode (publicZero k w) x) = encode (publicZero k w) (feed T bits x) := by
  cases x with
  | failed | running => rfl
  | finished st log =>
    cases st with
    | none => rfl
    | some v => simp only [feedBytes,encode,finish,feed,start_spec,Bool.cond_true]; rfl

def pass (base : Memory w) (fuel : ℕ) (x : Model w p r) (bits : Bits.Word) : Model w p r :=
  (modelStep T (publicZero k w) base)^[fuel] (feed T bits x)

private def native (base : Memory w) (fuel : ℕ)
    : Option (Option (Word w) × Stores w) → Bits.Word → Option (Option (Word w) × Stores w)
  | some (some v,log), bits =>
    let P := (T.instantiate w (publicZero k w)).program
    (execute P fuel (P.start v) (memory base log) bits).map fun rep => (rep.result,storeEvents log rep.events)
  | _, _ => none

private theorem pass_result (base : Memory w) (fuel : ℕ) (x : Model w p r) (bits : Bits.Word) :
    result (pass T base fuel x bits) = native T base fuel (result x) bits := by
  have bad := Function.iterate_fixed (f:=modelStep T (publicZero k w) base) (x:=Model.failed) rfl fuel
  cases x with
  | failed | running => simp [pass,feed,bad,result,native]
  | finished st log =>
    cases st with
    | none => simp [pass,feed,bad,result,native]
    | some v => exact result_iterate T _ base fuel _ bits log

private theorem fold_bad (base : Memory w) (fuel : ℕ) (tapes : List Bits.Word) :
    tapes.foldl (native T base fuel) none = none := by
  induction tapes with
  | nil => rfl
  | cons b bs ih => exact ih

private theorem fold_some (base : Memory w) (fuel : ℕ) (tapes : List Bits.Word) (st : Option (Word w)) (log : Stores w) :
    tapes.foldl (native T base fuel) (some (st,log)) =
      (runSegment (T.instantiate w (publicZero k w)).program fuel st (memory base log) tapes).map
        (fun rs => (endState st rs,storeEvents log (eventLog rs))) := by
  induction tapes generalizing st log with
  | nil => rfl
  | cons bs more ih =>
    cases st with
    | none => exact fold_bad T base fuel more
    | some v =>
      simp only [List.foldl_cons,native,runSegment]
      cases h : execute (T.instantiate w (publicZero k w)).program fuel
          ((T.instantiate w (publicZero k w)).program.start v) (memory base log) bs with
      | none => exact fold_bad T base fuel more
      | some rep =>
        simp only [Option.map_some]
        rw [ih,memory_storeEvents]
        cases runSegment (T.instantiate w (publicZero k w)).program fuel rep.result (after (memory base log) rep.events) more with
        | none => rfl
        | some rs =>
          simp only [Option.map_some,endState,eventLog,List.flatMap_cons,storeEvents,List.foldl_append]

/-- Rejection, the final persistent word, and every external write agree with
native replay after an arbitrary list of call tapes. -/
theorem chain_result (base : Memory w) (fuel : ℕ) (tapes : List Bits.Word) (st : Option (Word w)) (log : Stores w) :
    result (tapes.foldl (pass T base fuel) (.finished st log)) =
      (runSegment (T.instantiate w (publicZero k w)).program fuel st (memory base log) tapes).map
        (fun rs => (endState st rs,storeEvents log (eventLog rs))) := by
  have eq (bs : List Bits.Word) (x : Model w p r) :
      result (bs.foldl (pass T base fuel) x) = bs.foldl (native T base fuel) (result x) := by
    induction bs generalizing x with
    | nil => rfl
    | cons b bs ih => simp only [List.foldl_cons,ih,pass_result]
  rw [eq]
  exact fold_some T base fuel tapes st log

theorem feed_load (bits : Bits.Word) (x : Model w p r) : load (feed T bits x) ≤ load x+bits.length := by
  cases x with
  | failed | running => simp [feed,load]
  | finished st log => cases st <;> simp [feed,load,Machine.logProgram,Nat.add_comm]

theorem chain_load (base : Memory w) (fuel : ℕ) (tapes : List Bits.Word) (x : Model w p r) :
    load (tapes.foldl (pass T base fuel) x) ≤ load x+(tapes.map List.length).sum+2*fuel*tapes.length := by
  induction tapes generalizing x with
  | nil => simp
  | cons bs more ih =>
    have a := ih (pass T base fuel x bs)
    have b := load_iterate T (publicZero k w) base (feed T bs x) fuel
    have c := feed_load T bs x
    change load (pass T base fuel x bs) ≤ _ at b
    simp only [List.foldl_cons,List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

end
end OAI.Computability.MultitapeWeakETH.CallProgram
