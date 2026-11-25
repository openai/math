import OAI.Optimization.LinearProgramming.RAM.CallableOddCalls
import OAI.Optimization.LinearProgramming.RAM.CallableControl
import OAI.Optimization.LinearProgramming.RAM.CallableWindow

/-! A fixed native call can return a scalar computed by the callee into persistent
caller storage. The caller's other registers and the callee's final memory are preserved. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

/-- Invoke a single-tag program and copy one even scalar into the caller's odd bank. -/
def scalarResultCall (p : Program) (src dst : ℕ) : Fragment :=
  .seq (Fragment.invoke p 1 (Odd.sink (.scalar dst (fun _ => 0))))
    (Fragment.ofBlock (.op (.copy (Odd.slot dst) (2*src))))

private theorem putData_last {K : Type*} (m : Memory K) (dst : ℕ) (x y : K) :
    (m.putData dst x).putData dst y = m.putData dst y := by
  cases m with
  | mk data index =>
    have h : Function.update (Function.update data dst x) dst y = Function.update data dst y := by
      funext j
      by_cases hj : j=dst <;> simp [Function.update,hj]
    simp [Memory.putData,h]

/-- The final cross-bank copy is charged. Every intermediate scalar satisfies the
same predicate, and the finite footprint of the even bank is available for reuse. -/
theorem scalarResultCall_prepared {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p : Program} {dims : List ℕ} {xs : List K} {k : ℕ} {tr : Fin (k+1) → State K}
    (src dst : ℕ) (caller : Memory K) (P : K → Prop) (hc : caller.AllData P)
    (ht : Trace p (start dims xs) k tr) (ho : (tr (Fin.last k)).output=some 0)
    (hs : ∀ i j, P ((tr i).data j)) :
    let last := (tr (Fin.last k)).memory
    (scalarResultCall p src dst).Run P (Odd.memory (start dims xs).memory caller) (2*k+3)
        (Odd.memory last (caller.putData dst (last.data src))) ∧
      Footprint (nativeWindow p dims xs + k) (last.atPC 0) := by
  let last := (tr (Fin.last k)).memory
  let tmp := caller.putData dst 0
  have hinit : P ((start dims xs).data xs.length) := by
    rw [← ht.1]
    exact hs 0 _
  have hz : P 0 := by simpa [start] using hinit
  have htmp : tmp.AllData P := hc.putData dst hz
  have hlast : last.AllData P := hs _
  have hret : ((TagSink.scalar dst (fun _ => 0)).store 0 caller).AllData P := by
    simpa [TagSink.store,tmp] using htmp
  have run := Odd.invoke_packed 1 (.scalar dst (fun _ => 0)) P caller dims xs tr (by decide)
    hc ht hs ho hret
  have run' :
      (Fragment.invoke p 1 (Odd.sink (.scalar dst (fun _ => 0)))).Run P
        (Odd.memory (start dims xs).memory caller) (2*k+2) (Odd.memory last tmp) := by
    simpa [last,tmp,TagSink.store] using run
  have hcopy : Block.Eval (Memory.AllData P) (.op (.copy (Odd.slot dst) (2*src)))
      (Odd.memory last tmp) 1 (Odd.memory last (tmp.putData dst (last.data src))) := by
    apply Block.Eval.op (Odd.allData _ _ hlast htmp) (Odd.allData _ _ hlast (htmp.putData _ (hlast src)))
    intro pc
    change some (((Odd.memory last tmp).putData (Odd.slot dst)
      ((Odd.memory last tmp).data (2*src))).atPC (pc+1)) = _
    simp
  have copied := run'.seq (Fragment.Run.ofBlock hcopy)
  rw [show tmp.putData dst (last.data src) = caller.putData dst (last.data src) from putData_last ..] at copied
  exact ⟨copied,nativeWindow_trace ht le_rfl⟩

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
