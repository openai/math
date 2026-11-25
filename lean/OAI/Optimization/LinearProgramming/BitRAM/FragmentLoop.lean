import OAI.Optimization.LinearProgramming.BitRAM.DispatchLoop
import OAI.Optimization.LinearProgramming.RAM.CallableControl

/-! The finite bit-program loop linked to an arbitrary relocatable ordinary RAM fragment. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch
open RAM RAM.Callable OracleSpec

/-- Restore the sentinel after each invocation, so a linked routine can use the loop scratch. -/
def fragmentLoop (p : BitProgram) (body : Fragment) : Fragment :=
  let reset := Fragment.ofBlock (.op (.addrConst limitReg p.states))
  .seq reset (.loop (.addrLT 39 limitReg) (.seq body reset))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem reset_fragment {p : BitProgram} {P : K → Prop} {m : Memory K}
    (safe : ∀ j, P (m.data j)) :
    (Fragment.ofBlock (.op (.addrConst limitReg p.states))).Run P m 1 (m.putIndex limitReg p.states) :=
  Fragment.Run.ofBlock (P := P) (reset_limit (p := p) (safe := fun s => ∀ j, P (s.data j)) safe safe)

/-- Simulate every source tick in any outer program. The count includes the guard, reset and
back jump at each iteration plus the entry reset and final false guard. -/
theorem fragmentLoop_correct {p : BitProgram} {bo : WordOracle} {P : K → Prop} {body : Fragment}
    (inv : p.Config → Memory K → Prop) (factor : Nat)
    (valid : ∀ c m, inv c m → ∀ j, P (m.data j))
    (pcValue : ∀ c (m : Memory K), inv c m → m.index 39 = c.pc.elim p.states Fin.val)
    (restores : ∀ c m, inv c m → inv c (m.putIndex limitReg p.states))
    (one : ∀ c c' n, p.tick bo c = some (n,c') → ∀ m, inv c m →
      ∃ t, body.Run P m (factor*n) t ∧ inv c' t)
    {c d : p.Config} {cost : Nat} (source : p.Run bo c cost d) (halted : d.pc = none)
    {m : Memory K} (initial : inv c m) :
    ∃ t, (fragmentLoop p body).Run P m ((factor+3)*cost+2) t ∧ inv d t := by
  let reset := Fragment.ofBlock (.op (.addrConst limitReg p.states))
  let loop := Fragment.loop (.addrLT 39 limitReg) (.seq body reset)
  have inside {s u : p.Config} {n : Nat} (r : p.Run bo s n u) :
      u.pc = none → ∀ a : Memory K, inv s a → a.index limitReg = p.states →
        ∃ t, loop.Run P a ((factor+3)*n+1) t ∧ inv u t := by
    induction r with
    | refl s =>
      intro stop a ha lim
      have test : (Cond.addrLT 39 limitReg).test a = false := by
        simp [Cond.test,pcValue s a ha,stop,lim]
      exact ⟨a,by simpa using Fragment.Run.loopFalse test (valid s a ha) (.seq body reset),ha⟩
    | @step s s' u tail cost edge _ ih =>
      intro stop a ha lim
      obtain ⟨q,pc⟩ := tick_running edge
      have test : (Cond.addrLT 39 limitReg).test a = true := by
        simp [Cond.test,pcValue s a ha,pc,lim]
      obtain ⟨mid,stepRun,hmid⟩ := one s s' cost edge a ha
      have back := reset_fragment (p := p) stepRun.safe_end
      obtain ⟨t,rest,last⟩ := ih stop (mid.putIndex limitReg p.states) (restores s' mid hmid) (by simp)
      have whole := Fragment.Run.loopTrue test (stepRun.seq back) rest
      refine ⟨t,whole.mono ?_,last⟩
      have pos := tick_positive edge
      simp only [Nat.mul_add, Nat.add_mul]
      omega
  have beginRun := reset_fragment (p := p) (valid c m initial)
  obtain ⟨t,rest,last⟩ := inside source halted (m.putIndex limitReg p.states) (restores c m initial) (by simp)
  exact ⟨t,(beginRun.seq rest).mono (by omega),last⟩

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI
