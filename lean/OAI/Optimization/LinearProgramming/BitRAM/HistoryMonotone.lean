import OAI.Optimization.LinearProgramming.BitRAM.DispatchSource
import Lean.Elab.Tactic.Omega

/-! Every reached request of a completed deterministic run belongs to its final raw
transcript. A silent final postcondition therefore excludes all external calls. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
open OracleSpec

private theorem tick_past {p : BitProgram} {o : WordOracle} {a b : p.Config} {k : Nat}
    (e : p.tick o a=some (k,b)) : a.transcript.length≤b.transcript.length := by
  cases hpc : a.pc with
  | none => simp [BitProgram.tick,hpc] at e
  | some q =>
    cases h : p.instruction q (a.store (p.scan q)).head? <;>
      simp [BitProgram.tick,hpc,h] at e <;> obtain ⟨rfl,rfl⟩ := e <;> simp

private theorem tick_past_cost {p : BitProgram} {o : WordOracle} {a b : p.Config} {k : Nat}
    (e : p.tick o a=some (k,b)) : b.transcript.length≤a.transcript.length+k := by
  cases hpc : a.pc with
  | none => simp [BitProgram.tick,hpc] at e
  | some q =>
    cases hop : p.instruction q (a.store (p.scan q)).head? <;>
      simp [BitProgram.tick,hpc,hop] at e <;> obtain ⟨rfl,rfl⟩ := e <;> simp
    omega

private theorem tick_past_mem {p : BitProgram} {o : WordOracle} {a b : p.Config} {k : Nat}
    (edge : p.tick o a=some (k,b)) {qa : Word×Word} (hm : qa∈a.transcript) : qa∈b.transcript := by
  cases hpc : a.pc with
  | none => simp [BitProgram.tick,hpc] at edge
  | some q =>
    cases hop : p.instruction q (a.store (p.scan q)).head? <;>
      simp [BitProgram.tick,hpc,hop] at edge <;> obtain ⟨rfl,rfl⟩ := edge <;>
      first | exact hm | exact List.mem_cons_of_mem _ hm

theorem run_past {p : BitProgram} {o : WordOracle} {a b : p.Config} {k : Nat}
    (r : p.Run o a k b) : a.transcript.length≤b.transcript.length := by
  induction r with
  | refl => exact le_rfl
  | step edge _ ih => exact (tick_past edge).trans ih

theorem run_past_cost {p : BitProgram} {o : WordOracle} {a b : p.Config} {k : Nat}
    (r : p.Run o a k b) : b.transcript.length≤a.transcript.length+k := by
  induction r with
  | refl => simp
  | step edge _ ih => have := tick_past_cost edge; omega

theorem run_past_mem {p : BitProgram} {o : WordOracle} {a b : p.Config} {k : Nat}
    (r : p.Run o a k b) {qa : Word×Word} : qa∈a.transcript → qa∈b.transcript := by
  induction r with
  | refl => exact id
  | step edge _ ih => exact fun hm => ih (tick_past_mem edge hm)

/-- Every configuration reached from the start of a halting run can still run to
the same terminal configuration. -/
theorem remainder_of_halted {p : BitProgram} {o : WordOracle} {a b : p.Config} {k : Nat}
    (full : p.Run o a k b) : b.pc=none → ∀ u j, p.Run o a j u → ∃ rem, p.Run o u rem b := by
  induction full with
  | refl a =>
    intro done u j earlier
    cases earlier with
    | refl => exact ⟨0,.refl _⟩
    | step edge _ => simp [BitProgram.tick,done] at edge
  | step first tail ih =>
    intro done u j earlier
    cases earlier with
    | refl => exact ⟨_,.step first tail⟩
    | step edge rest =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (edge.symm.trans first))
      exact ih done _ _ rest

/-- The real issued input-answer pair occurs in the fully completed raw history, and
there is still room for at least this one query beyond the reached prefix. -/
theorem request_mem_final {p : BitProgram} {o : WordOracle} {a b : p.Config} {k : Nat}
    (full : p.Run o a k b) (done : b.pc=none) (u : p.Config) (j : Nat) (q next : Fin p.states)
    (earlier : p.Run o a j u) (pc : u.pc=some q)
    (ask : p.instruction q (u.store (p.scan q)).head? = .ask next) :
    (u.bufferRev.reverse,o u.transcript u.bufferRev.reverse)∈b.transcript ∧ u.transcript.length<b.transcript.length := by
  obtain ⟨rem,tail⟩ := remainder_of_halted full done u j earlier
  cases tail with
  | refl => simp_all
  | step edge after =>
    have actual := Dispatch.tick_ask (bo:=o) pc ask
    obtain ⟨_,eq⟩ := Prod.mk.inj (Option.some.inj (edge.symm.trans actual))
    rw [eq] at after
    refine ⟨run_past_mem after (by simp [Dispatch.answered]),?_⟩
    have grows : u.transcript.length+1 ≤ b.transcript.length := by simpa [Dispatch.answered] using run_past after
    omega

theorem no_request_of_silent_run {p : BitProgram} {o : WordOracle} {a b : p.Config} {k : Nat}
    (full : p.Run o a k b) (done : b.pc=none) (silent : b.transcript.length=a.transcript.length)
    (u : p.Config) (j : Nat) (q next : Fin p.states) (earlier : p.Run o a j u) (pc : u.pc=some q)
    (ask : p.instruction q (u.store (p.scan q)).head? = .ask next) : False := by
  have growth := (request_mem_final full done u j q next earlier pc ask).2
  have old := run_past earlier
  omega

/-- Turn a final-transcript postcondition into the local typed-ask and remaining-call
bound needed to invoke a numerical RAM service on the actual bit machine. -/
theorem permitted_of_transcript_post {p : BitProgram} {o : WordOracle} {w : Word} {budget : Nat}
    {post : Transcript→Word→Prop} {good : Word×Word→Prop} (source : p.ComputesWithin o w budget post)
    (typed : ∀ h out, post h out → ∀ qa∈h, good qa)
    (u : p.Config) (j : Nat) (q next : Fin p.states) (earlier : p.Run o (p.initial w) j u)
    (pc : u.pc=some q) (ask : p.instruction q (u.store (p.scan q)).head? = .ask next) :
    good (u.bufferRev.reverse,o u.transcript u.bufferRev.reverse) ∧ u.transcript.length<budget := by
  obtain ⟨k,d,full,within,done,final⟩ := source
  obtain ⟨present,strict⟩ := request_mem_final full done u j q next earlier pc ask
  have limit : d.transcript.length ≤ k := by simpa [BitProgram.initial] using run_past_cost full
  exact ⟨typed _ _ final _ present,by omega⟩

theorem permitted_of_transcript {p : BitProgram} {o : WordOracle} {w : Word} {budget : Nat} {good : Word→Prop}
    (source : p.ComputesWithin o w budget (fun h _ => ∀ qa∈h, good qa.1))
    (u : p.Config) (j : Nat) (q next : Fin p.states) (earlier : p.Run o (p.initial w) j u)
    (pc : u.pc=some q) (ask : p.instruction q (u.store (p.scan q)).head? = .ask next) :
    good u.bufferRev.reverse ∧ u.transcript.length<budget :=
  permitted_of_transcript_post (good:=fun qa => good qa.1) source (fun _ _ ok => ok) u j q next earlier pc ask

end BitRAM
end LinearProgramming
end Optimization
end OAI
