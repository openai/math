import OAI.Optimization.LinearProgramming.Recovery.BitEpoch

/-! Compose the sealed finite PCG bit time across interrupted epochs, carrying the
actual minor service forward. Each epoch can use its own simultaneous hidden costs. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace BitEpoch

open OracleSpec
variable {S : Type*}

/-- The real prefix to the first interrupt of a source run is `scan`. Only the final
noninterrupted epoch consumes the sign written by the bit machine. -/
inductive Completed (p : BitProgram) (input : Word) (serve : S→Word→Reply S) (sign : Bool) :
    S → List ℕ → List (Event Word) → S → Prop where
  | finish {s : S} {k : ℕ} {last : p.Config} :
      p.Run (fun h q=>[reply serve s h q]) (p.initial input) k last → last.pc=none →
      (scan serve s last.transcript).stopped=false → last.bufferRev.reverse=[sign] →
      Completed p input serve sign s [k] (scan serve s last.transcript).events (scan serve s last.transcript).state
  | retry {s t : S} {k : ℕ} {last : p.Config} {costs : List ℕ} {log : List (Event Word)} :
      p.Run (fun h q=>[reply serve s h q]) (p.initial input) k last → last.pc=none →
      (scan serve s last.transcript).stopped=true → Completed p input serve sign (scan serve s last.transcript).state costs log t →
      Completed p input serve sign s (k::costs) ((scan serve s last.transcript).events++log) t

/-- The bit-time sum bounds every attempted epoch, including its genuinely executed
truncated prefix. All recorded requested words are actual well-formed price queries. -/
theorem repeated_sealed_epochs {p : BitProgram} {N R budget cap : ℕ} (anchor : Fin N) (sign : Bool)
    (serve : S→Word→Reply S) (initial : S)
    (pcg : ∀ f : Transcript→Word→Bool,p.ComputesWithin (fun h q=>[f h q]) (priceInput R anchor) budget (pricePost R anchor))
    (restartCap : ∀ ev s,ServicePath serve initial ev s → restartCount ev ≤ cap)
    (clean : ∀ prior s,ServicePath serve initial prior s → ∀ ev t,ServicePath serve s ev t → restartCount ev=0 →
      ∃ active : Set (Fin N),∃ costs : Fin N→ℕ,anchor∈active ∧ (∀ j∈active,costs j ≤ R) ∧ priceConsistent sign active costs (wordHistory ev)) :
    ∃ costs log t, Completed p (priceInput R anchor) serve sign initial costs log t ∧ ServicePath serve initial log t ∧
      costs.length ≤ cap+1 ∧ costs.sum ≤ (cap+1)*budget ∧ log.length ≤ costs.sum ∧
      ∀ e∈log,∃ i : Fin N,∃ prices : Fin N→ℚ,e.1=priceQuery i prices := by
  have go (fuel : ℕ) : ∀ (prior : List (Event Word)) (s : S), ServicePath serve initial prior s →
      restartCount prior+fuel=cap → ∃ costs log t, Completed p (priceInput R anchor) serve sign s costs log t ∧
        ServicePath serve s log t ∧ costs.length ≤ fuel+1 ∧ costs.sum ≤ (fuel+1)*budget ∧ log.length ≤ costs.sum ∧
        ∀ e∈log,∃ i : Fin N,∃ prices : Fin N→ℚ,e.1=priceQuery i prices := by
    induction fuel using Nat.strong_induction_on with
    | h f ih =>
      intro prior s past room
      obtain ⟨k,hk,last,run,halt,path,len,well,num,done⟩:=sealed_epoch anchor sign serve s pcg (clean prior s past)
      let a:=scan serve s last.transcript
      cases stop : a.stopped with
      | false =>
        refine ⟨[k],a.events,a.state,.finish run halt stop (done stop),path,by simp,?_,by simpa using len,well⟩
        simpa only [List.sum_cons,List.sum_nil,Nat.add_zero] using hk.trans (Nat.le_mul_of_pos_left budget (by omega))
      | true =>
        have count : restartCount a.events=1 := by simpa only [show (scan serve s last.transcript).stopped=true from stop,Bool.toNat_true] using num
        have global:=restartCap _ _ (past.append path)
        rw [restartCount_append] at global
        change restartCount prior+restartCount a.events ≤ cap at global
        have pos : 0 < f := by omega
        have left : restartCount (prior++a.events)+(f-1)=cap := by rw [restartCount_append,count];omega
        obtain ⟨times,log,t,rest,body,len',cost',calls',well'⟩:=ih (f-1) (by omega) _ _ (past.append path) left
        refine ⟨k::times,a.events++log,t,.retry run halt stop rest,path.append body,?_,?_,?_,?_⟩
        · simp only [List.length_cons];omega
        · simp only [List.sum_cons,Nat.add_mul,Nat.one_mul]
          rw [show f-1+1=f by omega] at cost';omega
        · simp only [List.length_append,List.sum_cons]
          exact Nat.add_le_add (show a.events.length ≤ k from len) calls'
        · intro e he;rcases List.mem_append.mp he with h|h
          · exact well e h
          · exact well' e h
  exact go cap [] initial (.nil _) (by simp)

end BitEpoch
end Recovery
end LinearProgramming
end Optimization
end OAI
