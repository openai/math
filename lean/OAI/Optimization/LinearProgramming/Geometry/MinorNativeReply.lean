import OAI.Optimization.LinearProgramming.Geometry.MinorReplyMemory
import OAI.Optimization.LinearProgramming.RAM.CallableOddBlock

/-! Convert the native service's return tag and scalar into the published
scalar-oracle response while keeping both logical register banks persistent. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall

open RAM RAM.Callable OracleSpec

private def stopReply : Block := Odd.block (Block.straight [.const 2 0,.addrConst 83 1])

private def valueReply : Block :=
  .seq (Odd.block (.op (.incr 83 82))) <|
  .seq (.op (.store (Odd.slot 83) 0)) (Odd.block (.op (.addrConst 83 2)))

/-- The first packet word is the return tag. Returning a value copies physical
register zero, the native scalar output, into the next odd-bank packet cell. -/
def replyBlock : Block :=
  .seq (.op (.store (Odd.slot 82) (Odd.slot 2)))
    (.branch (.scalarLT (Odd.slot 29) (Odd.slot 2)) stopReply valueReply)

private theorem memory_eq {K : Type*} {a b : Memory K} (h : ∀ j, a.data j=b.data j)
    (g : ∀ j, a.index j=b.index j) : a=b :=
  congrArg₂ Memory.mk (funext h) (funext g)

private theorem restoreTag (m : Memory ℚ) (b : ℕ) (hb : 35 ≤ b) (hz : m.data 2=0) (q : ℚ) :
    ((m.putData 2 q).putData b q).putData 2 0=m.putData b q := by
  refine memory_eq ?_ (fun _ => rfl)
  intro j
  by_cases hj : j=2
  · simp [hj,show 2≠b by omega,hz]
  by_cases h : j=b
  · simp [h,show b≠2 by omega]
  · simp [hj,h]

private theorem clearTag (m : Memory ℚ) (hz : m.data 2=0) : m.putData 2 0=m := by
  refine memory_eq ?_ (fun _ => rfl)
  intro j
  by_cases hj : j=2 <;> simp [hj,hz]

private theorem physical_header (P : ℚ → Prop) (z : State ℚ) (a : Memory ℚ)
    (hs : z.memory.AllData P) (ha : a.AllData P) :
    Block.Eval (Memory.AllData P) (.op (.store (Odd.slot 82) (Odd.slot 2))) (Odd.memory z.memory a) 1
      (Odd.memory z.memory (a.putData (a.index 82) (a.data 2))) := by
  have ok := Odd.allData z.memory a hs ha
  have e := Block.Eval.op_store (Odd.memory z.memory a) (Odd.slot 82) (Odd.slot 2) ok
    (ok.putData _ (ok (Odd.slot 2)))
  simpa only [Odd.index_slot,Odd.data_slot,Odd.putData] using e

private theorem restart_run (P : ℚ → Prop) (z : State ℚ) (m : Memory ℚ)
    (hs : z.memory.AllData P) (hm : m.AllData P) (h0 : P 0) :
    ∃ k ≤ 8, Block.Eval (Memory.AllData P) stopReply (Odd.memory z.memory m) k
      (Odd.memory z.memory ((m.putData 2 0).putIndex 83 1)) := by
  have e := Block.Eval.op_const m 2 (0:ℚ) hm (hm.putData 2 h0)
  have a := Block.Eval.op_addrConst (m.putData 2 0) 83 1 e.safe_end (e.safe_end.putIndex 83 1)
  have shape : Block.Eval (Memory.AllData P) (Block.straight [.const 2 0,.addrConst 83 1]) m 2
     ((m.putData 2 0).putIndex 83 1) := e.seq (a.seq (.skip a.safe_end))
  exact Odd.block_eval P z.memory hs shape

private theorem numeric_run (P : ℚ → Prop) (z : State ℚ) (m : Memory ℚ) (q : ℚ)
    (hs : z.memory.AllData P) (hm : m.AllData P) (hv : z.data 0=q) :
    ∃ k ≤ 9, Block.Eval (Memory.AllData P) valueReply (Odd.memory z.memory m) k
      (Odd.memory z.memory (((m.putIndex 83 (m.index 82+1)).putData (m.index 82+1) q).putIndex 83 2)) := by
  let a := m.putIndex 83 (m.index 82+1)
  let b := a.putData (m.index 82+1) q
  have inc := Block.Eval.op_incr m 83 82 hm (hm.putIndex 83 (m.index 82+1))
  obtain ⟨i,hi,ei⟩ := Odd.block_eval P z.memory hs inc
  have x : (Odd.memory z.memory a).data 0=q := (Odd.data_even z.memory a 0).trans hv
  have store : Block.Eval (Memory.AllData P) (.op (.store (Odd.slot 83) 0))
      (Odd.memory z.memory a) 1 (Odd.memory z.memory b) := by
    have ok := Odd.allData z.memory a hs (hm.putIndex 83 _)
    have es := Block.Eval.op_store _ (Odd.slot 83) 0 ok (ok.putData _ (ok 0))
    simpa only [b,Odd.index_slot,show a.index 83=m.index 82+1 from Memory.putIndex_same ..,x,
      Odd.putData] using es
  have hb : b.AllData P := (hm.putIndex 83 _).putData _ (hv ▸ hs 0)
  have finish := Block.Eval.op_addrConst b 83 2 hb (hb.putIndex 83 2)
  obtain ⟨l,hl,el⟩ := Odd.block_eval P z.memory hs finish
  exact ⟨i+(1+l),by omega,ei.seq (store.seq el)⟩

/-- Both branches implement the exact received packet of the sealed scalar
oracle. All registers in the even native bank survive. The caller's scratch
tag is restored before returning control. -/
theorem replyBlock_eval (P : ℚ → Prop) (z : State ℚ) (ans : Option ℚ) (caller : Memory ℚ)
    (emitted : MinorLog.emits z ans) (nativeSafe : z.memory.AllData P) (callerSafe : caller.AllData P)
    (h0 : P 0) (h1 : P 1) (hbase : 35 ≤ caller.index 82) (h2 : caller.data 2=0) (h29 : caller.data 29=0) :
    ∃ k ≤ 42, Block.Eval (Memory.AllData P) replyBlock
      (Odd.memory z.memory (responseSink.store (responseTag ans) caller)) k
      (Odd.memory z.memory (OracleSegments.received caller 82 83 (BorderBatch.reply ans))) := by
  cases ans with
  | none =>
    let a := caller.putData 2 1
    let b := a.putData (caller.index 82) 1
    have hb : b.AllData P := (callerSafe.putData 2 h1).putData _ h1
    have step₁ : Block.Eval (Memory.AllData P) (.op (.store (Odd.slot 82) (Odd.slot 2)))
        (Odd.memory z.memory a) 1 (Odd.memory z.memory b) := by
      simpa only [a,b,Memory.putData_index,Memory.putData_same] using
        physical_header P z a nativeSafe (callerSafe.putData 2 h1)
    have guard : (Cond.scalarLT (Odd.slot 29) (Odd.slot 2)).test (Odd.memory z.memory b)=true := by
      simp [Cond.test,b,a,show 29≠caller.index 82 by omega,show 2≠caller.index 82 by omega,h29]
    obtain ⟨k,hk,yes⟩ := restart_run P z b nativeSafe hb h0
    have hend : (b.putData 2 0).putIndex 83 1=OracleSegments.received caller 82 83 (BorderBatch.reply none) := by
      rw [received_none,show b.putData 2 0=caller.putData (caller.index 82) 1 from restoreTag caller _ hbase h2 1]
    refine ⟨1+(1+k+1),by omega,?_⟩
    have run := step₁.seq (Block.Eval.branchTrue (b := valueReply) guard yes)
    rw [hend] at run
    exact run
  | some q =>
    let b := caller.putData (caller.index 82) 0
    have hb : b.AllData P := callerSafe.putData _ h0
    have step₁ : Block.Eval (Memory.AllData P) (.op (.store (Odd.slot 82) (Odd.slot 2)))
        (Odd.memory z.memory caller) 1 (Odd.memory z.memory b) := by
      simpa only [b,h2] using physical_header P z caller nativeSafe callerSafe
    have guard : (Cond.scalarLT (Odd.slot 29) (Odd.slot 2)).test (Odd.memory z.memory b)=false := by
      simp [Cond.test,b,show 29≠caller.index 82 by omega,show 2≠caller.index 82 by omega,h29,h2]
    obtain ⟨k,hk,no⟩ := numeric_run P z b q nativeSafe hb emitted.2.1
    have hend : ((b.putIndex 83 (b.index 82+1)).putData (b.index 82+1) q).putIndex 83 2 =
        OracleSegments.received caller 82 83 (BorderBatch.reply (some q)) := by
      rw [received_some]
      refine memory_eq (fun _ => rfl) ?_
      intro j
      by_cases hj : j=83 <;> simp [hj,b]
    refine ⟨1+(1+k),by omega,?_⟩
    have run := step₁.seq (Block.Eval.branchFalse (a := stopReply) guard no)
    rw [hend] at run
    change Block.Eval _ _ (Odd.memory z.memory (caller.putData 2 0)) _ _
    rw [clearTag caller h2]
    exact run

end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI
