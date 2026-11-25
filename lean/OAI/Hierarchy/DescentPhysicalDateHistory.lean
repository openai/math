import OAI.Hierarchy.DescentPublicDateMachine
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! # The state at every date of one fixed native public program -/
namespace Hierarchy.DescentSixParty.Chronology.DateCode
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
open scoped Classical BigOperators
variable {w : ℕ}

theorem same_output (d : DateCode w) {m m₁ m₂ : Memory w} (one : d.Runs m m₁) (two : d.Runs m m₂) : m₁=m₂ :=by
  cases d with
  | ordinary p t q u=>
    obtain ⟨a,read,write⟩:=one
    obtain ⟨b,first,second⟩:=two
    have same:=ProtocolRAM.exec_unique p m a b read first
    subst b
    exact ProtocolRAM.exec_unique q a m₁ m₂ write second
  | reset p t=>exact ProtocolRAM.exec_unique p m m₁ m₂ one two

def nextMemory (d : DateCode w) (m : Memory w) :=
  if h:∃out,d.Runs m out then h.choose else m

theorem nextMemory_eq (d : DateCode w) {m out : Memory w} (run_ : d.Runs m out) : d.nextMemory m=out :=by
  have h:∃a,d.Runs m a:=⟨_,run_⟩
  rw [nextMemory,dite_eq_left h]
  exact d.same_output h.choose_spec run_

def history (date : ℕ→DateCode w) (m : Memory w) : ℕ→Memory w
  | 0=>m
  | t+1=>(date t).nextMemory (history date m t)

theorem history_step (date : ℕ→DateCode w) (m : Memory w) (i : ℕ)
    (total : ∃out,(date i).Runs (history date m i) out) :
    (date i).Runs (history date m i) (history date m (i+1)) :=by
  obtain ⟨out,h⟩:=total
  rw [history,(date i).nextMemory_eq h]
  exact h

theorem history_event (date : ℕ→DateCode w) (m : Memory w) (i : ℕ) {Q : Memory w→Prop}
    (fact : ∃out,(date i).Runs (history date m i) out ∧ Q out) : Q (history date m (i+1)) :=by
  obtain ⟨out,h,p⟩:=fact
  simpa only [history,(date i).nextMemory_eq h] using p

/-- A boot procedure can include the ten-tick initialization before it prints its other
source banks. Extending that procedure preserves every actual intermediate date memory. -/
def afterBoot (boot : Procedure w) (date : ℕ→DateCode w) : ℕ→Procedure w
  | 0=>boot
  | i+1=>(date i).extend (afterBoot boot date i)

def afterTicks (bootTicks : ℕ) (date : ℕ→DateCode w) : ℕ→ℕ
  | 0=>bootTicks
  | i+1=>afterTicks bootTicks date i+(date i).ticks

theorem boot_history (boot : Procedure w) (bootTicks : ℕ) (date : ℕ→DateCode w) (m start : Memory w)
    (booted : boot.Exec m start bootTicks) (n : ℕ)
    (total : ∀i<n,∀s,∃out,(date i).Runs s out) :
    (afterBoot boot date n).Exec m (history date start n) (afterTicks bootTicks date n) :=by
  induction n with
  | zero=>exact booted
  | succ n ih=>
    have prior : (afterBoot boot date n).Exec m (history date start n) (afterTicks bootTicks date n):=
      ih (fun i hi=>total i (hi.trans (Nat.lt_succ_self _)))
    have next_:=history_step date start n (total n (Nat.lt_succ_self _) _)
    cases eqn:date n with
    | ordinary body h meter t=>
      rw [eqn] at next_
      obtain ⟨mid,bodyRun,meterRun⟩:=next_
      simp only [afterBoot,afterTicks,eqn,extend,ticks,←Nat.add_assoc]
      intro P R K machine
      exact Procedure.Exec.then (Procedure.Exec.then prior bodyRun) meterRun machine
    | reset body h=>
      rw [eqn] at next_
      simp only [afterBoot,afterTicks,eqn,extend,ticks]
      intro P R K machine
      exact Procedure.Exec.then prior next_ machine

theorem after_cheap (boot : Procedure w) (date : ℕ→DateCode w) (n : ℕ)
    (initial : ProtocolRAM.CheapCode boot) (paid : ∀i<n,(date i).cheap) : ProtocolRAM.CheapCode (afterBoot boot date n):=by
  induction n with
  | zero=>exact initial
  | succ n ih=>
    have old : ProtocolRAM.CheapCode (afterBoot boot date n):=ih (fun i hi=>paid i (hi.trans (Nat.lt_succ_self _)))
    have new_:=paid n (Nat.lt_succ_self _)
    cases eqn:date n with
    | ordinary q a r b=>
      rw [eqn] at new_
      rw [afterBoot,eqn]
      intro P R K pc reg pub exit j
      exact ProtocolRAM.cheap_seq (ProtocolRAM.cheap_seq old new_.1) new_.2 pc reg pub exit j
    | reset q a=>
      rw [eqn] at new_
      rw [afterBoot,eqn]
      intro P R K pc reg pub exit j
      exact ProtocolRAM.cheap_seq old new_ pc reg pub exit j

theorem boot_bill (boot : Procedure w) (bootTicks n : ℕ) (date : ℕ→DateCode w) :
    (afterTicks bootTicks date n+7*DescentStaticWordColumn.names (afterBoot boot date n))*w=
      (bootTicks+7*DescentStaticWordColumn.names boot)*w+∑i∈Finset.range n,(date i).tariff :=by
  induction n with
  | zero=>simp only [afterTicks,afterBoot,Finset.range_zero,Finset.sum_empty,Nat.add_zero]
  | succ n ih=>
    rw [afterTicks,afterBoot,Finset.sum_range_succ,←Nat.add_assoc,←ih]
    cases eqn:date n <;> simp only [extend,tariff,ticks,names,DescentStaticWordColumn.names_seq] <;> ring

end
end Hierarchy.DescentSixParty.Chronology.DateCode

end OAI
