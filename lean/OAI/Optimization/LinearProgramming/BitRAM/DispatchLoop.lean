import OAI.Optimization.LinearProgramming.BitRAM.Dispatch

/-! Iterating a real encoded transition, including the RAM loop tests and access to the
fixed halt sentinel, simulates a complete bit-program run with a uniform step bound. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch
open RAM OracleSpec

def limitReg := 26

def controller (p : BitProgram) (body : Block) : Block :=
  .seq (.op (.addrConst limitReg p.states))
    (.loop (.addrLT 39 limitReg) (.seq body (.op (.addrConst limitReg p.states))))

theorem tick_positive {p : BitProgram} {o : WordOracle} {c d : p.Config} {k : ℕ}
    (hr : p.tick o c = some (k,d)) : 0 < k := by
  cases h : c.pc with
  | none => simp [BitProgram.tick,h] at hr
  | some q =>
    cases hi : p.instruction q (c.store (p.scan q)).head? <;>
      simp [BitProgram.tick,h,hi] at hr <;> omega

theorem tick_running {p : BitProgram} {o : WordOracle} {c d : p.Config} {k : ℕ}
    (hr : p.tick o c = some (k,d)) : ∃ q, c.pc = some q := by
  cases h : c.pc with
  | none => simp [BitProgram.tick,h] at hr
  | some q => exact ⟨q,rfl⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem reset_limit {safe : RAM.Memory K → Prop} {p : BitProgram} {m : RAM.Memory K}
    (h : safe m) (h' : safe (m.putIndex limitReg p.states)) :
    Block.Eval safe (.op (.addrConst limitReg p.states)) m 1 (m.putIndex limitReg p.states) :=
  .op h h' (fun _ => rfl)

/-- The simulation hypotheses describe executions of the actual RAM block. The controller rebuilds
the loop-limit scratch register after each callback and before the next test. -/
theorem controller_eval {p : BitProgram} {o : WordOracle} {body : Block}
    {safe : RAM.Memory K → Prop} (rep : p.Config → RAM.Memory K → Prop) (factor : ℕ)
    (valid : ∀ c m, rep c m → safe m)
    (pcValue : ∀ c m, rep c m → m.index 39 = c.pc.elim p.states Fin.val)
    (restores : ∀ c m, rep c m → rep c (m.putIndex limitReg p.states))
    (one : ∀ c c' n, p.tick o c = some (n,c') → ∀ m, rep c m →
      ∃ t k, k ≤ factor*n ∧ Block.Eval safe body m k t ∧ rep c' t)
    {c d : p.Config} {n : ℕ} (bitRun : p.Run o c n d) (halted : d.pc = none)
    {m : RAM.Memory K} (initial : rep c m) :
    ∃ t k, k ≤ (factor+3)*n+2 ∧ Block.Eval safe (controller p body) m k t ∧ rep d t := by
  let loop : Block := .loop (.addrLT 39 limitReg) (.seq body (.op (.addrConst limitReg p.states)))
  have inside {c d : p.Config} {n : ℕ} (run : p.Run o c n d) :
      d.pc = none → ∀ m : RAM.Memory K, rep c m → m.index limitReg = p.states →
        ∃ t k, k ≤ (factor+3)*n+1 ∧ Block.Eval safe loop m k t ∧ rep d t := by
    induction run with
    | refl c =>
      intro ended m hm lim
      refine ⟨m,1,by simp, Block.Eval.loopFalse ?_ (valid c m hm), hm⟩
      simp [Cond.test,pcValue c m hm,ended,lim]
    | @step c c' d tail cost step _ ih =>
      intro ended m hm lim
      obtain ⟨q,hq⟩ := tick_running step
      have test : (Cond.addrLT 39 limitReg).test m = true := by
        simp [Cond.test,pcValue c m hm,hq,lim]
      obtain ⟨m',elapsed,hk,physical,hm'⟩ := one c c' cost step m hm
      have hr := restores c' m' hm'
      obtain ⟨out,rest,ht,go,endRep⟩ := ih ended (m'.putIndex limitReg p.states) hr (by simp)
      have back := reset_limit (p := p) (valid c' m' hm') (valid c' _ hr)
      refine ⟨out,1+(elapsed+1)+1+rest,?_, Block.Eval.loopTrue test (physical.seq back) go,endRep⟩
      have pos := tick_positive step
      rw [show (factor+3)*(cost+tail)+1 = factor*cost + 3*cost + ((factor+3)*tail+1) by simp only [Nat.mul_add, Nat.add_mul, Nat.add_assoc]]
      omega
  have started := restores c m initial
  obtain ⟨out,ks,hk,run,result⟩ :=
    inside bitRun halted (m.putIndex limitReg p.states) started (by simp)
  refine ⟨out,1+ks,by omega, ?_,result⟩
  exact (reset_limit (p := p) (valid c m initial) (valid c _ started)).seq run

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI
