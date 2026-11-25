import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf
import OAI.Optimization.LinearProgramming.BitRAM.DispatchResumeFrame
import OAI.Optimization.LinearProgramming.BitRAM.NativeInterrupt

/-! A source PCG is the odd logical caller. Native numerical memory is framed even
at low scalar and index scratch addresses throughout every simulated bit instruction. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG

open RAM RAM.Tape RAM.Callable OracleSpec BitRAM

/-- Private logical bit-VM header. The caller's heap heads start at 65. -/
def statusReg : Nat := 45

def transfer (p : BitProgram) (handler : Fragment) : Fragment :=
  .seq (Odd.leaf preparePacket) (.seq handler (.branch (Odd.cond (.addrLT nilReg statusReg))
    (Odd.leaf .skip) (Odd.leaf (receiveReply p))))

def boundary (p : BitProgram) (handler : Fragment) : Fragment :=
  .seq (Odd.leaf (Dispatch.runUntilRequest p)) (.branch (Odd.cond (.addrLT nilReg askReg))
    (transfer p handler) (Odd.leaf .skip))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A maximal ordinary prefix followed by exactly one genuine numerical service, or
by the source halt. The same numerical state survives an ordinary prefix verbatim. -/
theorem boundary_run {p : BitProgram} {bo : WordOracle} {P : K→Prop} (handler : Fragment)
    {c d : p.Config} {time : ℕ} (source : p.Run bo c time d) (halted : d.pc=none)
    {m native : Memory K} (rep : Rep p c m) (safe : Good P m) (nativeSafe : native.AllData P)
    (post : Dispatch.Stop p→Memory K→Memory K→Prop) (budget : ℕ)
    (onHalt : ∀ s u,Dispatch.Prefix p c time (.halted s) → Rep p s u → u.data=m.data →
      StableHeaders m u → post (.halted s) native u)
    (onAsk : ∀ n s q u,Dispatch.Prefix p c n (.request s q) → Dispatch.Suffix bo n time d (.request s q) →
      Awaiting p s q u → Good P u → u.data=m.data → StableHeaders m u → ∃ next v,
      (transfer p handler).Run P (Odd.memory native u) budget (Odd.memory next v) ∧ post (.request s q) next v) :
    ∃ n stop next v,Dispatch.Prefix p c n stop ∧ Dispatch.Suffix bo n time d stop ∧
      (boundary p handler).Run P (Odd.memory native m) (4*((2*p.states+35)*(n+1)+2)+budget+2)
        (Odd.memory next v) ∧ post stop next v := by
  obtain ⟨n,stop,pre,suffix⟩:=Dispatch.prefix_of_run source halted
  obtain ⟨u,k,hk,run,present,data,high,_⟩:=Dispatch.runUntilRequest_complete_frame pre rep safe
  have first:=Odd.leaf_run P native nativeSafe run
  cases stop with
  | halted s =>
    have ready : Rep p s u := present
    have guard : (Odd.cond (.addrLT nilReg askReg)).test (Odd.memory native u)=false := by
      rw [Odd.cond_test]
      simp [Cond.test,ready.askReady]
    have pass:=Odd.leaf_run P native nativeSafe (Block.Eval.skip (show Good P u from run.safe_end))
    exact ⟨n,_,native,u,pre,suffix,(first.seq (Fragment.Run.branchFalse guard _ pass)).mono (by omega),
      onHalt s u (suffix.2 ▸ pre) ready data high⟩
  | request s q =>
    have pending : Awaiting p s q u:=present
    have guard : (Odd.cond (.addrLT nilReg askReg)).test (Odd.memory native u)=true := by
      rw [Odd.cond_test]
      simp [Cond.test,pending.heap.nilValue,pending.askFlag]
    obtain ⟨next,v,call,done⟩:=onAsk n s q u pre suffix pending run.safe_end data high
    exact ⟨n,_,next,v,pre,suffix,(first.seq (Fragment.Run.branchTrue guard call _)).mono (by omega),done⟩

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
