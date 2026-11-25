import OAI.Optimization.LinearProgramming.Recovery.OddEpochStep
import OAI.Optimization.LinearProgramming.OracleSpec.CompilerProof

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG
open RAM RAM.Tape RAM.Callable OracleSpec BitRAM
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Execute a *whole* ordinary PCG prefix, its real numerical callback if reached, and
the sentinel update. A source answer pays for further iterations, while the first
actual restart returns a terminal receipt immediately. -/
theorem epoch_advance {p : BitProgram} {bo : WordOracle} {P : K → Prop} {env : Environment K}
    {ack cut : Receipt p K} {handler : Fragment} {start last : p.Config} {budget : ℕ}
    (service : Handles p bo P env ack cut handler start last budget) (ended : last.pc=none)
    (x : Cursor p K) (outer : Memory K) (active : Active p bo P env start last x outer) :
    ∃ t k, (Fragment.seq (boundary p handler) (Odd.leaf (finishCode p statusReg))).Run P outer k t ∧
      ((∃ z : Last p K, epochGuard.test t=false ∧ Out p P env last z t ∧
          ServiceTrace p bo ack cut x.source x.native z.1 z.2 ∧ 1+k+1 ≤ epochUnit p budget*(x.left+1)) ∨
        ∃ y : Cursor p K, Active p bo P env start last y t ∧ y.left<x.left ∧
          1+k+1 ≤ epochUnit p budget*(x.left-y.left) ∧ ∀ z : Last p K,
            ServiceTrace p bo ack cut y.source y.native z.1 z.2 →
            ServiceTrace p bo ack cut x.source x.native z.1 z.2) := by
  obtain ⟨⟨used,reached⟩,src,m,rfl,live,_⟩ := active
  obtain ⟨n,z,next,v,pre,suffix,body,post⟩ := physical_boundary service ended reached src live
  have unit := boundaryCost_le p budget n
  cases z with
  | halted s =>
    obtain ⟨same,h⟩ := post
    subst next
    let after := v.putIndex Dispatch.limitReg p.states
    have adjust := finish_answer (p := p) statusReg h.vmSafe h.nativeSafe h.represented.heap.nilValue h.clean
    have current : Live p P env s x.native after := h.refresh
    have pc : s.pc=none := prefix_action pre
    have code : after.index stateReg=p.states := by simpa only [pcCode,pc,Option.elim] using current.represented.stateCode
    have limit : after.index Dispatch.limitReg=p.states := Memory.putIndex_same _ _ _
    have test : epochGuard.test (Odd.memory x.native after)=false := by
      simp only [epochGuard,Odd.cond_test]
      simp [Cond.test,code,limit]
    exact ⟨_,_,body.seq adjust,Or.inl ⟨(.halted s,x.native),test,⟨after,rfl,suffix.1,current,code⟩,
      .halted pre,by simpa only [suffix.2] using unit⟩⟩
  | request s q =>
    cases post with
    | interrupted why nsafe vsafe nil flag ports =>
      let after := (v.putIndex stateReg p.states).putIndex Dispatch.limitReg p.states
      have adjust := finish_restart (p := p) (native := next) statusReg vsafe nsafe nil flag
      have code : after.index stateReg=p.states :=
        (Memory.putIndex_ne _ (by decide : stateReg≠Dispatch.limitReg) _).trans (Memory.putIndex_same _ _ _)
      have limit : after.index Dispatch.limitReg=p.states := Memory.putIndex_same _ _ _
      have flagEq : after.index statusReg=v.index statusReg :=
        (Memory.putIndex_ne _ (by decide : statusReg≠Dispatch.limitReg) _).trans
          (Memory.putIndex_ne _ (by decide : statusReg≠stateReg) _)
      have nilEq : after.index nilReg=v.index nilReg :=
        (Memory.putIndex_ne _ (by decide : nilReg≠Dispatch.limitReg) _).trans
          (Memory.putIndex_ne _ (by decide : nilReg≠stateReg) _)
      have framed : StableHeaders v after := by
        intro i low _
        exact (Memory.putIndex_ne _ (show i≠Dispatch.limitReg by unfold Dispatch.limitReg;omega) _).trans
          (Memory.putIndex_ne v (show i≠stateReg by unfold stateReg;omega) _)
      have retained := env.preserve v after rfl framed ports
      have test : epochGuard.test (Odd.memory next after)=false := by
        simp only [epochGuard,Odd.cond_test]
        simp [Cond.test,code,limit]
      have enough := Nat.mul_le_mul_left (epochUnit p budget) (Nat.add_le_add_right (Dispatch.prefix_le_time suffix) 1)
      exact ⟨_,_,body.seq adjust,Or.inl ⟨(.request s q,next),test,⟨after,rfl,flagEq ▸ flag,code,nsafe,vsafe,retained,nilEq.trans nil⟩,
        .interrupted pre why,unit.trans enough⟩⟩
    | answered why h =>
      obtain ⟨left,account,tail⟩ := suffix
      obtain ⟨pc,atPC,ask⟩ := prefix_action pre
      let y : Cursor p K := ⟨Dispatch.answered bo s q,next,left⟩
      let after := v.putIndex Dispatch.limitReg p.states
      have adjust := finish_answer (p := p) statusReg h.vmSafe h.nativeSafe h.represented.heap.nilValue h.clean
      have passed := ((reached.append (pre.run bo)).append
        (BitProgram.Run.single (Dispatch.tick_ask (bo := bo) atPC ask)))
      have nextActive : Active p bo P env start last y (Odd.memory next after) :=
        ⟨⟨_,passed⟩,tail,after,rfl,h.refresh,Memory.putIndex_same _ _ _⟩
      have pos : 0<Dispatch.chargedAsk bo s := by unfold Dispatch.chargedAsk;omega
      have less : left<x.left := by omega
      have enough := Nat.mul_le_mul_left (epochUnit p budget) (show n+1≤x.left-left by omega)
      exact ⟨_,_,body.seq adjust,Or.inr ⟨y,nextActive,less,unit.trans enough,
        fun z path => ServiceTrace.answered pre why path⟩⟩

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
