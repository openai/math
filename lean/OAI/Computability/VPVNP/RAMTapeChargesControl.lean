import OAI.Computability.VPVNP.RAMTapeChargesValue
import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Tactic.DeriveFintype

/-!
# Finite control for metering RAM calls and probes

One dispatch removes one unary fuel mark. Starting a call and taking a probe
use the same charge entry: remove a call mark and a site mark, subtract one
from the binary global allowance, and increment the binary cumulative cost.
No branch of the control iterates to the numerical value of a binary word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Charges

/-- Stack labels for dispatch fuel, call and site credits, binary global and cumulative
counters, and arithmetic scratch. -/
inductive Port where
  | fuel | call | site | globalLeft | cost | tmp
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Metering control for dispatch, unary credit removal, binary carry or borrow, and counter
restoration. -/
inductive State where
  | dispatch | charge | site
  | scan (up carry : Bool) | emit (up bit carry : Bool)
  | restore (up overflow : Bool) | put (up bit overflow : Bool)
  | done | reject
  deriving DecidableEq, Fintype

/-- Reject overflow after restoration, finish after incrementing cost, or begin incrementing
cost after decrementing the global budget. -/
def resume (up overflow : Bool) : State :=
  if overflow then .reject else if up then .done else .scan true true

/-- Meter a dispatch by one fuel mark, or charge a call or probe against the call, site,
global, and cumulative counters. -/
def code : StackCode Port State
  | .dispatch => .pop .fuel (fun | none => .reject | some _ => .done)
  | .charge => .pop .call (fun | none => .reject | some _ => .site)
  | .site => .pop .site (fun | none => .reject | some _ => .scan false true)
  | .scan up carry => .pop (if up then .cost else .globalLeft)
      (fun | none => .restore up carry | some b => .emit up (b ^^ carry) (nextCarry up carry b))
  | .emit up bit carry => .push .tmp bit (.scan up carry)
  | .restore up overflow => .pop .tmp
      (fun | none => resume up overflow | some b => .put up b overflow)
  | .put up bit overflow => .push (if up then .cost else .globalLeft) bit (.restore up overflow)
  | .done => .halt true
  | .reject => .halt false

/-- Contents of the unary allowances, binary charge counters, and scratch stack used by the
metering control. -/
structure Data where
  /-- Unary instruction fuel, with one mark removed for each dispatch. -/
  fuel : List Bool
  /-- Remaining unary charge marks for the current call. -/
  call : List Bool
  /-- Remaining unary charge marks for the site. -/
  site : List Bool
  /-- Binary global allowance decremented by one per charge. -/
  globalLeft : List Bool
  /-- Binary cumulative cost incremented by one per charge. -/
  cost : List Bool
  /-- Reversed output bits saved while updating a binary counter. -/
  tmp : List Bool

/-- Read a metering stack from its named counter or scratch field. -/
def Data.stacks (s : Data) : Stacks Port
  | .fuel => s.fuel
  | .call => s.call
  | .site => s.site
  | .globalLeft => s.globalLeft
  | .cost => s.cost
  | .tmp => s.tmp

/-- Update a single metering stack in the charge bank. -/
def Data.set (s : Data) : Port → List Bool → Data
  | .fuel, x => {s with fuel := x}
  | .call, x => {s with call := x}
  | .site, x => {s with site := x}
  | .globalLeft, x => {s with globalLeft := x}
  | .cost, x => {s with cost := x}
  | .tmp, x => {s with tmp := x}

theorem Data.set_stacks (s : Data) (i : Port) (xs : List Bool) :
    (s.set i xs).stacks = Function.update s.stacks i xs := by
  funext j
  cases i <;> cases j <;> rfl

/-- A continuing deterministic transition. Halting states have no successor. -/
def tick (q : State) (s : Data) : Option (State × Data) :=
  match code q with
  | .pop k f => some (f (s.stacks k).head?, s.set k (s.stacks k).tail)
  | .push k b next => some (next, s.set k (b :: s.stacks k))
  | .goto next => some (next, s)
  | .choose _ _ | .halt _ => none

/-- An execution of the charge controller between two states and banks in exactly the given
number of stack steps. -/
abbrev Run (n : ℕ) (q : State) (s : Data) (q' : State) (t : Data) :=
  StackRuns code n q s.stacks q' t.stacks

theorem prepend {q q' q'' : State} {s t u : Data} {n : ℕ}
    (h : tick q s = some (q', t)) (hr : Run n q' t q'' u) : Run (n + 1) q s q'' u := by
  apply StackRuns.cons _ hr
  unfold tick at h
  cases hc : code q with
  | push k b next =>
    rw [hc] at h
    cases h
    rw [Data.set_stacks]
    exact .push hc
  | pop k f =>
    rw [hc] at h
    cases h
    rw [Data.set_stacks]
    exact .pop hc
  | goto next => rw [hc] at h; cases h; exact .goto hc
  | choose | halt => simp [hc] at h

/-- Choose the active binary counter without disturbing the other counter. -/
def scanData (up : Bool) (f a s other bits tmp : List Bool) : Data :=
  if up then ⟨f,a,s,other,bits,tmp⟩ else ⟨f,a,s,bits,other,tmp⟩

private theorem firstPass (up carry : Bool) (bits tmp f a s other : List Bool) :
    let t := adjust up carry bits
    Run (2 * bits.length + 1) (.scan up carry) (scanData up f a s other bits tmp)
      (.restore up t.2) (scanData up f a s other [] (t.1.reverse ++ tmp)) := by
  induction bits generalizing tmp carry with
  | nil => cases up <;> exact prepend rfl (.nil ..)
  | cons b bits ih =>
    dsimp only
    rw [adjust_cons]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons, Nat.mul_succ]
    have h := ih (nextCarry up carry b) ((b ^^ carry) :: tmp)
    cases up <;> exact prepend rfl (prepend rfl h)

private theorem restorePass (up overflow : Bool) (tmp bits f a s other : List Bool) :
    Run (2 * tmp.length + 1) (.restore up overflow) (scanData up f a s other bits tmp)
      (resume up overflow) (scanData up f a s other (tmp.reverse ++ bits) []) := by
  induction tmp generalizing bits with
  | nil => cases up <;> exact prepend rfl (.nil ..)
  | cons b tmp ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons, Nat.mul_succ]
    have h := ih (b :: bits)
    cases up <;> exact prepend rfl (prepend rfl h)

/-- Exact runtime of the binary update, with overflow and underflow flags
preserved all the way to the terminating control decision. -/
theorem adjustRun (up carry : Bool) (bits f a s other : List Bool) :
    let t := adjust up carry bits
    Run (4 * bits.length + 2) (.scan up carry) (scanData up f a s other bits [])
      (resume up t.2) (scanData up f a s other t.1 []) := by
  have h := firstPass up carry bits [] f a s other
  have hr := restorePass up (adjust up carry bits).2 (adjust up carry bits).1.reverse [] f a s other
  simp only [List.append_nil] at h
  simp only [List.length_reverse, adjust_length, List.reverse_reverse, List.append_nil] at hr
  convert h.trans hr using 1
  omega

end RAMTape.Charges

end VPVNP
end Computability
end OAI
