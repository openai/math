import OAI.Optimization.LinearProgramming.RAM.CallableControl
import OAI.Optimization.LinearProgramming.Compression.SignWireReply

/-! Export a three-way comparison through native halt tags, so a surrounding
caller can isolate the entire numerical procedure in its even register bank. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM RAM.Callable

private def ternaryProgram (f : Fragment) (low mid : Cond) : Program :=
  f.emit 0 ++ [low.instr (f.size+2) (f.size+1), mid.instr (f.size+3) (f.size+4),
    .halt 0, .halt 1, .halt 2]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem endTrace {P : K → Prop} {prog : Program} {s : State K} {m : Memory K} {k pc tag : ℕ}
    (exec : Execution prog (fun st => ∀ i,P (st.data i)) s k (m.atPC pc))
    (hf : prog[pc]?=some (.halt tag)) :
    ∃ tr : Fin (k+1+1) → State K, Trace prog s (k+1) tr ∧
      (tr (Fin.last (k+1))).output=some tag ∧ (tr (Fin.last (k+1))).memory=m ∧
      ∀ i j,P ((tr i).data j) := by
  let t : State K := {m.atPC pc with output:=some tag}
  have stop : Execution prog (fun st => ∀ i,P (st.data i)) (m.atPC pc) 1 t :=
    .one exec.safe_end (by simp [step,Memory.atPC,hf,execInstr,t]) exec.safe_end
  obtain ⟨tr,ht,last,hs⟩ := (exec.append stop).to_trace
  exact ⟨tr,ht,last ▸ rfl,last ▸ rfl,hs⟩

private theorem ternary_trace {f : Fragment} {P : K → Prop} {s t : Memory K} {B : ℕ}
    (ef : f.Run P s B t) (low mid : Cond) :
    ∃ k ≤ B+3, ∃ tr : Fin (k+1) → State K, Trace (ternaryProgram f low mid) (s.atPC 0) k tr ∧
      (tr (Fin.last k)).output=some (if low.test t then 0 else if mid.test t then 1 else 2) ∧
      (tr (Fin.last k)).memory=t ∧ ∀ i j,P ((tr i).data j) := by
  let prog := ternaryProgram f low mid
  have whole : CodeAt prog 0 (f.emit 0 ++ [low.instr (f.size+2) (f.size+1),
      mid.instr (f.size+3) (f.size+4), .halt 0,.halt 1,.halt 2]) := CodeAt.whole _
  obtain ⟨k,hk,run⟩ := ef prog 0 whole.left
  simp only [Nat.zero_add] at run
  have tail := whole.right
  rw [f.length_emit,Nat.zero_add] at tail
  have tail₁ := Block.Eval.tail_at tail
  have tail₂ := Block.Eval.tail_at tail₁
  have tail₃ := Block.Eval.tail_at tail₂
  have tail₄ := Block.Eval.tail_at tail₃
  have e₀ := Block.Eval.test_exec (safe:=fun m : Memory K => ∀ j,P (m.data j))
    prog low t f.size (f.size+2) (f.size+1) run.safe_end tail.head
  cases hl : low.test t with
  | true =>
    simp only [hl,ite_true] at e₀
    obtain ⟨tr,ht,ho,hm,hs⟩ := endTrace (run.append e₀) tail₂.head
    exact ⟨k+1+1,by omega,tr,ht,by simpa [hl] using ho,hm,hs⟩
  | false =>
    simp only [hl] at e₀
    have e₁ := Block.Eval.test_exec (safe:=fun m : Memory K => ∀ j,P (m.data j))
      prog mid t (f.size+1) (f.size+3) (f.size+4) run.safe_end tail₁.head
    cases hm : mid.test t with
    | true =>
      simp only [hm,ite_true] at e₁
      obtain ⟨tr,ht,ho,he,hs⟩ := endTrace ((run.append e₀).append e₁) tail₃.head
      exact ⟨k+1+1+1,by omega,tr,ht,by simpa [hl,hm] using ho,he,hs⟩
    | false =>
      simp only [hm] at e₁
      obtain ⟨tr,ht,ho,he,hs⟩ := endTrace ((run.append e₀).append e₁) tail₄.head
      exact ⟨k+1+1+1,by omega,tr,ht,by simpa [hl,hm] using ho,he,hs⟩

/-- In the nested numerical caller, the ternary tag is logical address 14,
hence physical address 29 and value 2*tag+1. -/
def tagReturningProgram (f : Fragment) : Program :=
  ternaryProgram (.seq f (.ofBlock (.straight [.addrConst 0 3,.addrConst 2 5])))
    (.addrLT 29 0) (.addrLT 29 2)

theorem tagReturningProgram_trace_memory {f : Fragment} {P : K → Prop} {s t : Memory K} {B : ℕ}
    (ef : f.Run P s B t) (o : Ordering) (ho : t.index 29=2*comparisonTag o+1) :
    ∃ k ≤ B+5, ∃ tr : Fin (k+1) → State K, Trace (tagReturningProgram f) (s.atPC 0) k tr ∧
      (tr (Fin.last k)).output=some (comparisonTag o) ∧
      (tr (Fin.last k)).memory=(t.putIndex 0 3).putIndex 2 5 ∧ ∀ i j,P ((tr i).data j) := by
  let u := t.putIndex 0 3
  let v := u.putIndex 2 5
  have hu : u.AllData P := ef.safe_end
  have hv : v.AllData P := hu
  have e : Block.Eval (Memory.AllData P) (.straight [.addrConst 0 3,.addrConst 2 5]) t 2 v :=
    (Block.Eval.op_addrConst t 0 3 ef.safe_end hu).seq ((Block.Eval.op_addrConst u 2 5 hu hv).seq (.skip hv))
  obtain ⟨k,hk,tr,ht,hout,last,hs⟩ := ternary_trace (ef.seq (Fragment.Run.ofBlock e)) (.addrLT 29 0) (.addrLT 29 2)
  refine ⟨k,by omega,tr,ht,?_,last,hs⟩
  cases o <;> simpa [Cond.test,v,u,ho,comparisonTag] using hout

theorem tagReturningProgram_trace {f : Fragment} {P : K → Prop} {s t : Memory K} {B : ℕ}
    (ef : f.Run P s B t) (o : Ordering) (ho : t.index 29=2*comparisonTag o+1) :
    ∃ k ≤ B+5, ∃ tr : Fin (k+1) → State K, Trace (tagReturningProgram f) (s.atPC 0) k tr ∧
      (tr (Fin.last k)).output=some (comparisonTag o) ∧ ∀ i j,P ((tr i).data j) := by
  obtain ⟨k,hk,tr,ht,tag,_,safe⟩ := tagReturningProgram_trace_memory ef o ho
  exact ⟨k,hk,tr,ht,tag,safe⟩

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
