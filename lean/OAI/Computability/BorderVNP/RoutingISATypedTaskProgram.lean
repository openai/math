import OAI.Computability.BorderVNP.RoutingISATypedTaskSetup
import OAI.Computability.BorderVNP.RoutingISATypedTaskStep
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # End-to-end native execution of the typed cell-task producer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The fixed word-RAM table publishes the true compact local task count and every
global owner. Its work is bounded by a fixed number of ordinary ticks per public cell. -/
theorem program_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (hp : (pub 0).val=l.frame)
    (fields : l.Fields (readings m)) (room : l.Room (readings m) w) :
    BoundedRun pub mac program s m (setup.slots+l.cells*(body.slots+1)+2)
      (fun z => z.mem=l.published (readings m)) := by
  let original := readings m
  let P := fun i (z : NatState) => l.Ready i (l.before original i) z ∧ z.mem=l.image original i
  have runSetup := (setup_run pub mac s m l hp fields room).mono le_rfl (Q := P 0) (fun _ h => h)
  have loop (u : Bank w) (mu : Memory w) (start : P 0 (.ofWords u mu)) :
      BoundedRun pub mac (.whileLt 18 5 body) u mu (l.cells*(body.slots+1)+1) (P l.cells) := by
    apply run_counted_loop pub mac 18 5 body l.cells body.slots P _ _ 0 (Nat.zero_le _) u mu start
    · intro i z h
      exact ⟨h.1 18 (by decide),h.1 5 (by decide)⟩
    · intro i hi z mz h
      exact body_step l original room pub mac i hi z mz h.1 h.2
  have tail (u : Bank w) (mu : Memory w) (start : P 0 (.ofWords u mu)) :
      BoundedRun pub mac (.seq (.whileLt 18 5 body) (.store 17 19)) u mu (l.cells*(body.slots+1)+1+1)
        (fun z => z.mem=l.published original) := by
    apply (loop u mu start).seq
    rintro v mv ⟨ready,eqmem⟩
    have addr : (.ofWords v mv : NatState).reg 17=l.frame+90 := ready 17 (by decide)
    have len : (.ofWords v mv : NatState).reg 19=l.before original l.cells := ready 19 (by decide)
    apply ((Code.store 17 19).runFixed pub mac v mv trivial).mono le_rfl
    rintro out rfl
    simp only [Code.fixedEval,addr,len,eqmem,Layout.published]
  exact (runSetup.seq tail).mono (by omega) (fun _ h => h)

/-- The machine produces a unique positive, deterministic trace with no private choices
while building the task table. -/
theorem native_program {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (hp : (pub 0).val=l.frame)
    (fields : l.Fields (readings m)) (room : l.Room (readings m) w) :
    ∃ es t mt, Runs pub mac program s m es t mt ∧ readings mt=l.published (readings m) ∧
      traceCost es ≤ setup.slots+l.cells*(body.slots+1)+2 ∧
      (∀ e ∈ es, e.choices=[] ∧ e.sign=.plus) ∧
      (∀ bits fs, TeamRAM.execute (program.program.fetch pub mac) ⟨0,s⟩ m bits = some fs ↔
        fs=es ∧ bits=es.map TeamRAM.Event.choices) := by
  obtain ⟨es,t,mt,run,cost,output⟩ := program_run pub mac s m l hp fields room
  refine ⟨es,t,mt,run,output,cost,run.unsigned_events (by decide),?_⟩
  intro bits fs
  rw [Code.execute_iff_runs (by decide : program.withoutAccept=true)]
  constructor
  · rintro ⟨⟨u,mu,r⟩,hbits⟩
    obtain ⟨rfl,_,_⟩ := r.unique_of_deterministic (by decide) run
    exact ⟨rfl,hbits.symm⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨⟨t,mt,run⟩,rfl⟩

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
