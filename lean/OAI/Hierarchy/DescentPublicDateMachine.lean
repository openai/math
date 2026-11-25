import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.DescentPrivateHeader
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Fixed public instructions, exact clock and instruction bill for all dates -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators
noncomputable section

/-- Ordinary dates finish with the private multiplicity store. A reset executes
its compiled body and keeps the same private register. -/
inductive DateCode (w : ℕ) where
  | ordinary (main : Procedure w) (mainTicks : ℕ) (store : Procedure w) (storeTicks : ℕ)
  | reset (main : Procedure w) (mainTicks : ℕ)

namespace DateCode
variable {w : ℕ}

def extend (d : DateCode w) (prior : Procedure w) := match d with
  | .ordinary main _ store _=>(prior.seq main).seq store
  | .reset main _=>prior.seq main

def ticks : DateCode w→ℕ
  | .ordinary _ n _ t=>n+t
  | .reset _ n=>n

def names : DateCode w→ℕ
  | .ordinary main _ store _=>DescentStaticWordColumn.names main+DescentStaticWordColumn.names store
  | .reset main _=>DescentStaticWordColumn.names main

def tariff (d : DateCode w) := (d.ticks+7*d.names)*w

def cheap : DateCode w→Prop
  | .ordinary main _ store _=>ProtocolRAM.CheapCode main ∧ ProtocolRAM.CheapCode store
  | .reset main _=>ProtocolRAM.CheapCode main

/-- The computation may use a different memory at each date. Term and duration
are determined by the public date index alone, including on malformed proposals. -/
def Runs (d : DateCode w) (old new : Memory w) := match d with
  | .ordinary main n store t=>∃mid,main.Exec old mid n ∧ store.Exec mid new t
  | .reset main n=>main.Exec old new n

def compile (privateAt : ℕ) (date : ℕ→DateCode w) : ℕ→Procedure w
  | 0=>DescentPrivateHeader.clearHeader w privateAt
  | n+1=>(date n).extend (compile privateAt date n)

def clock (date : ℕ→DateCode w) : ℕ→ℕ
  | 0=>10
  | n+1=>clock date n+(date n).ticks

theorem native {a n : ℕ} (date : ℕ→DateCode w) (m : Memory w)
    (room : a+1<2^w) (out : ℕ→Memory w) (seed : out 0=DescentPrivateHeader.initialized a m)
    (steps : ∀i<n,(date i).Runs (out i) (out (i+1))) :
    (compile a date n).Exec m (out n) (clock date n) := by
  induction n with
  | zero=>rw [seed];exact DescentPrivateHeader.initialize_run a m room
  | succ n ih=>
    have prior : (compile a date n).Exec m (out n) (clock date n) :=ih (fun i hi=>steps i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have last:=steps n (Nat.lt_succ_self n)
    cases eqn:date n with
    | ordinary main t store u=>
      rw [eqn] at last
      obtain ⟨mid,first,second⟩:=last
      simp only [compile,clock,eqn,extend,ticks,←Nat.add_assoc]
      intro P R K machine
      exact Procedure.Exec.then (Procedure.Exec.then prior first) second machine
    | reset main t=>
      rw [eqn] at last
      simp only [compile,clock,eqn,extend,ticks]
      intro P R K machine
      exact Procedure.Exec.then prior last machine

/-- Totality on every initialized caller memory does not require an accepted choice
or even a nonempty type of accepted choices. The native geometry sets each output. -/
theorem any {a n : ℕ} (date : ℕ→DateCode w) (m : Memory w) (room : a+1<2^w)
    (each : ∀i<n,∀old,∃new,(date i).Runs old new) :
    ∃out,(compile a date n).Exec m out (clock date n) := by
  induction n with
  | zero=>exact ⟨_,DescentPrivateHeader.initialize_run a m room⟩
  | succ n ih=>
    obtain ⟨old,prior⟩:=ih (fun i hi=>each i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    obtain ⟨out,last⟩:=each n (Nat.lt_succ_self n) old
    refine ⟨out,?_⟩
    cases eqn:date n with
    | ordinary main t store u=>
      rw [eqn] at last
      obtain ⟨mid,first,second⟩:=last
      simp only [compile,clock,eqn,extend,ticks,←Nat.add_assoc]
      intro P R K machine
      exact Procedure.Exec.then (Procedure.Exec.then prior first) second machine
    | reset main t=>
      rw [eqn] at last
      simp only [compile,clock,eqn,extend,ticks]
      intro P R K machine
      exact Procedure.Exec.then prior last machine

theorem cheap_compile (a n : ℕ) (date : ℕ→DateCode w) (hardware : ∀i<n,(date i).cheap) :
    ProtocolRAM.CheapCode (compile a date n) := by
  induction n with
  | zero=>exact @ProtocolRAM.scan_cheap w a 1 (.lit 0)
  | succ n ih=>
    have prev : ProtocolRAM.CheapCode (compile a date n):=ih (fun i hi=>hardware i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have last:=hardware n (Nat.lt_succ_self n)
    cases eqn:date n with
    | ordinary main t store u=>
      rw [eqn] at last
      rw [compile,eqn]
      intro P R K pc reg pub exit j
      exact ProtocolRAM.cheap_seq (ProtocolRAM.cheap_seq prev last.1) last.2 pc reg pub exit j
    | reset main t=>
      rw [eqn] at last
      rw [compile,eqn]
      intro P R K pc reg pub exit j
      exact ProtocolRAM.cheap_seq prev last pc reg pub exit j

/-- One private clear costs ten clocks and fifteen static names.
All other instructions are counted in exactly the date where they execute. -/
theorem billing (a n : ℕ) (date : ℕ→DateCode w) :
    (clock date n+7*DescentStaticWordColumn.names (compile a date n))*w=
      115*w+∑i∈Finset.range n,(date i).tariff := by
  induction n with
  | zero=>
    simp only [clock,compile,Finset.range_zero,Finset.sum_empty,Nat.add_zero,DescentPrivateHeader.clearHeader]
    rw [DescentStaticWordColumn.names_scan]
    rfl
  | succ n ih=>
    rw [clock,compile,Finset.sum_range_succ]
    rw [←Nat.add_assoc,←ih]
    cases eqn:date n with
    | ordinary main t store u=>
      simp only [extend,tariff,ticks,names,DescentStaticWordColumn.names_seq]
      ring
    | reset main t=>
      simp only [extend,tariff,ticks,names,DescentStaticWordColumn.names_seq]
      ring

end DateCode
end
end Hierarchy.DescentSixParty.Chronology

end OAI
