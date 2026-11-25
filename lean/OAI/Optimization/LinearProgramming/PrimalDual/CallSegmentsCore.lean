import OAI.Optimization.LinearProgramming.RAM.CallPrepared
import OAI.Optimization.LinearProgramming.PrimalDual.DecoderExit
import OAI.Optimization.LinearProgramming.RAM.EvalWeaken

/-! Count complete executions of installed feasibility subroutines. The comparison
uses their normal input, actual return tag, restored caller bank, and returned
scalar and address registers. Internal jumps do not constitute extra calls. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace CallSegments

open RAM RAM.Tape RAM.Block

abbrev Within (H : ℕ) := Good (fun x : ℚ => ratBits x ≤ H)

structure Returned (before after : Memory ℚ) (last : State ℚ) : Prop where
  data : ∀ i, after.data (2*i) = last.data i
  index : ∀ i, after.index (2*i) = 2*last.index i
  callerData : ∀ i, after.data (2*i+1) = before.data (2*i+1)
  callerIndex : ∀ i, after.index (2*i+1) = before.index (2*i+1)

/-- Isolate the installed instructions at their actual absolute addresses. A
prefix padding instruction halts, so a trace returning to a live caller can
fetch no instruction in that padding. -/
private def carrier (base : ℕ) (body : Program) : Program := List.replicate base (.halt 0) ++ body

private theorem inCarrier (base : ℕ) (body : Program) : CodeAt (carrier base body) base body :=
  ⟨List.replicate base (.halt 0),[],by simp,by simp [carrier]⟩

private theorem fetchAt {target body : Program} {base pc : ℕ} (placed : CodeAt target base body)
    (low : base ≤ pc) (high : pc < base+body.length) : target[pc]? = body[pc-base]? := by
  obtain ⟨pre,post,loc,rfl⟩ := placed
  have low' : pre.length ≤ pc := by simpa only [loc] using low
  have high' : pc < (pre++body).length := by simpa only [List.length_append,loc] using high
  rw [List.getElem?_append_left high',List.getElem?_append_right low',loc]

private theorem replay_inside {host body : Program} {base n : ℕ} {s : State ℚ} {tr : Fin (n+1) → State ℚ}
    (placed : CodeAt host base body) (localRun : Trace (carrier base body) s n tr)
    (liveLast : (tr (Fin.last n)).output = none) :
    Trace host s n tr ∧ ∀ i : Fin n, base ≤ (tr i.castSucc).pc ∧ (tr i.castSucc).pc < base+body.length := by
  have live (i : Fin n) : (tr i.castSucc).output = none := by
    have edge := localRun.2 i
    cases ho : (tr i.castSucc).output with
    | none => rfl
    | some _ => simp [step,ho] at edge
  have allLive (i : Fin (n+1)) : (tr i).output = none := by
    by_cases inside : i.val < n
    · let j : Fin n := ⟨i.val,inside⟩
      have same : j.castSucc = i := Fin.ext rfl
      exact same ▸ live j
    · have last : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [last]; exact liveLast
  have range (i : Fin n) : base ≤ (tr i.castSucc).pc ∧ (tr i.castSucc).pc < base+body.length := by
    let x := tr i.castSucc
    let y := tr i.succ
    have edge : step (carrier base body) x = some y := localRun.2 i
    have before : x.output = none := live i
    have after : y.output = none := allLive i.succ
    constructor
    · by_contra h
      have hlow : x.pc < base := Nat.lt_of_not_ge h
      have fetch : (carrier base body)[x.pc]? = some (.halt 0) := by
        unfold carrier
        rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hlow :
          x.pc < (List.replicate base (Instr.halt 0)).length)]
        exact List.getElem?_replicate_of_lt hlow
      have changed : {x with output := some 0} = y := by
        simpa only [step,before,fetch,execInstr,Option.some.injEq] using edge
      have impossible := congrArg State.output changed
      change some 0 = y.output at impossible
      rw [after] at impossible
      cases impossible
    · by_contra h
      have beyond : (carrier base body).length ≤ x.pc := by
        simpa only [carrier,List.length_append,List.length_replicate] using Nat.le_of_not_gt h
      have absent : (carrier base body)[x.pc]? = none := List.getElem?_eq_none beyond
      simp only [step,before,absent,reduceCtorEq] at edge
  refine ⟨⟨localRun.1,?_⟩,range⟩
  intro i
  have r := range i
  have agree := (fetchAt placed r.1 r.2).trans (fetchAt (inCarrier base body) r.1 r.2).symm
  simpa only [step,agree] using localRun.2 i

theorem unique_trace {p : Program} {s : State ℚ} {k : ℕ} {a b : Fin (k+1) → State ℚ}
    (left : Trace p s k a) (right : Trace p s k b) : a = b := by
  funext i
  induction i using Fin.induction with
  | zero => exact left.1.trans right.1.symm
  | succ j ih =>
    have edge := left.2 j
    rw [ih] at edge
    exact Option.some.inj (edge.symm.trans (right.2 j))

/-- A compiled wrapper block fetches only its own words before reaching the
following live instruction, also when installed inside a larger host program. -/
theorem fixedBlock_confined {host : Program} {H pc n : ℕ} {b : Block} {u v : Memory ℚ}
    (placed : CodeAt host pc (b.compile pc)) (work : Block.Eval (Within H) b u n v) :
    ∃ tr : Fin (n+1) → State ℚ, Trace host (u.atPC pc) n tr ∧ tr (Fin.last n) = v.atPC (pc+b.size) ∧
      ∀ i : Fin n, pc ≤ (tr i.castSucc).pc ∧ (tr i.castSucc).pc < pc+b.size := by
  obtain ⟨raw,r,last,_⟩ := (work.compile_correct (inCarrier pc (b.compile pc))).to_trace
  obtain ⟨actual,range⟩ := replay_inside placed r (congrArg State.output last)
  exact ⟨raw,actual,last,fun i => ⟨(range i).1,by simpa only [Block.length_compile] using (range i).2⟩⟩

structure Embedded (host guest : Program) (H base : ℕ) (ret : ℕ → ℕ) (dims : List ℕ) (xs : List ℚ)
    (valid : State ℚ → Prop) (tag : ℕ) (before after : Memory ℚ) (n : ℕ) : Prop where
  placed : CodeAt host base (Call.subroutine guest base ret)
  inputData : ∀ i, before.data (2*i) = (start dims xs).data i
  inputIndex : ∀ i, before.index (2*i) = 2*(start dims xs).index i
  virtual : ∃ (k : ℕ) (tr : Fin (k+1) → State ℚ), Trace guest (start dims xs) k tr ∧
    valid (tr (Fin.last k)) ∧ (tr (Fin.last k)).output = some tag ∧ n ≤ 2*k ∧
    (∀ i, scalarBound H (tr i)) ∧ Returned before after (tr (Fin.last k))
  confined : ∃ tr : Fin (n+1) → State ℚ, Trace host (before.atPC base) n tr ∧
    tr (Fin.last n) = after.atPC (ret tag) ∧ ∀ i : Fin n, base ≤ (tr i.castSucc).pc ∧
      (tr i.castSucc).pc < base+(Call.subroutine guest base ret).length
  physical : Execution host (scalarBound H) (before.atPC base) n (after.atPC (ret tag))

theorem record {host guest : Program} {H base k tag : ℕ} {ret : ℕ → ℕ} {dims : List ℕ} {xs : List ℚ}
    {valid : State ℚ → Prop} (before : Memory ℚ) (placed : CodeAt host base (Call.subroutine guest base ret))
    (data : ∀ i, before.data (2*i) = (start dims xs).data i)
    (index : ∀ i, before.index (2*i) = 2*(start dims xs).index i) (safe : Within H before)
    (tr : Fin (k+1) → State ℚ) (run : Trace guest (start dims xs) k tr)
    (bounds : ∀ i, scalarBound H (tr i)) (answer : valid (tr (Fin.last k)))
    (tagged : (tr (Fin.last k)).output = some tag) :
    ∃ n ≤ 2*k, ∃ after, Embedded host guest H base ret dims xs valid tag before after n ∧
      Returned before after (tr (Fin.last k)) := by
  obtain ⟨n,hn,after,localRun,a,b,c,d⟩ := Call.invoke_prepared_trace before dims xs (fun x => ratBits x ≤ H)
    (inCarrier base (Call.subroutine guest base ret)) data index safe tr run bounds tagged
  have result : Returned before after (tr (Fin.last k)) := ⟨a,b,c,d⟩
  obtain ⟨inner,localTrace,last,small⟩ := localRun.to_trace
  have stillLive : (inner (Fin.last n)).output = none := congrArg State.output last
  obtain ⟨actual,range⟩ := replay_inside placed localTrace stillLive
  have replay : Execution host (scalarBound H) (before.atPC base) n (after.atPC (ret tag)) :=
    last ▸ Execution.of_trace actual small
  exact ⟨n,hn,after,⟨placed,data,index,⟨k,tr,run,answer,tagged,hn,bounds,result⟩,
    ⟨inner,actual,last,range⟩,replay⟩,result⟩

inductive Part where
  | fixed (pc : ℕ) (block : Block)
  | embedded (pc : ℕ) (ret : ℕ → ℕ) (dims : List ℕ) (input : List ℚ) (valid : State ℚ → Prop) (tag : ℕ)
  | terminal (pc : ℕ) (block : Block) (tag : ℕ)

def count : List Part → ℕ
  | [] => 0
  | .embedded _ _ _ _ _ _ :: tail => count tail+1
  | _ :: tail => count tail

def stopped (m : Memory ℚ) (pc tag : ℕ) : State ℚ := {m.atPC pc with output := some tag}

inductive Realizes (host guest : Program) (H : ℕ) : Part → State ℚ → ℕ → State ℚ → Prop where
  | fixed {pc : ℕ} {b : Block} {u v : Memory ℚ} {k : ℕ} (placed : CodeAt host pc (b.compile pc)) (work : Block.Eval (Within H) b u k v) :
      Realizes host guest H (.fixed pc b) (u.atPC pc) k (v.atPC (pc+b.size))
  | embedded {pc ret dims input valid tag u v k} (work : Embedded host guest H pc ret dims input valid tag u v k) :
      Realizes host guest H (.embedded pc ret dims input valid tag) (u.atPC pc) k (v.atPC (ret tag))
  | terminal {pc : ℕ} {b : Block} {tag : ℕ} {u v : Memory ℚ} {k : ℕ} (placed : CodeAt host pc (b.compile pc ++ [.halt tag]))
      (work : Block.Eval (Within H) b u k v) :
      Realizes host guest H (.terminal pc b tag) (u.atPC pc) (k+1) (stopped v (pc+b.size) tag)

theorem Realizes.execution {host guest H part s k t} (h : Realizes host guest H part s k t) :
    Execution host (scalarBound H) s k t := by
  cases h with
  | fixed placed work => exact work.compile_correct placed
  | embedded work => exact work.physical
  | @terminal pc b tag u v k placed work =>
    have fetch := placed.right.head
    rw [Block.length_compile] at fetch
    have halt : Execution host (scalarBound H) (v.atPC (pc+b.size)) 1 (stopped v (pc+b.size) tag) :=
      .one work.safe_end (by simp [step,Memory.atPC,fetch,execInstr,stopped]) work.safe_end
    exact (work.compile_correct placed.left).append halt

inductive Joined (host guest : Program) (H : ℕ) : List Part → State ℚ → ℕ → State ℚ → Prop where
  | nil {s} (safe : scalarBound H s) : Joined host guest H [] s 0 s
  | cons {p ps s u v k l} (part : Realizes host guest H p s k u) (tail : Joined host guest H ps u l v) :
      Joined host guest H (p :: ps) s (k+l) v

theorem Joined.single {host guest H p s k t} (h : Realizes host guest H p s k t) :
    Joined host guest H [p] s k t := .cons h (.nil h.execution.safe_end)

theorem Joined.append {host guest H ps qs s u t k l} (h : Joined host guest H ps s k u)
    (g : Joined host guest H qs u l t) : Joined host guest H (ps++qs) s (k+l) t := by
  induction h with
  | nil _ => simpa using g
  | cons part _ ih => simpa only [List.cons_append,Nat.add_assoc] using Joined.cons part (ih g)

theorem Joined.execution {host guest H ps s k t} (h : Joined host guest H ps s k t) :
    Execution host (scalarBound H) s k t := by
  induction h with
  | nil hs => exact .done _ hs
  | cons part _ ih => exact part.execution.append ih

theorem widenBlock {h H b u k v} (run : Block.Eval (Within h) b u k v) (le : h ≤ H) :
    Block.Eval (Within H) b u k v := run.weaken (fun _ safe i => (safe i).trans le)

theorem record_widen {host guest h H pc ret dims input valid tag u v k}
    (work : Embedded host guest h pc ret dims input valid tag u v k) (le : h ≤ H) :
    Embedded host guest H pc ret dims input valid tag u v k := by
  obtain ⟨n,tr,run,out,ht,budget,bits,frame⟩ := work.virtual
  exact ⟨work.placed,work.inputData,work.inputIndex,
    ⟨n,tr,run,out,ht,budget,fun i j => (bits i j).trans le,frame⟩,work.confined,
    work.physical.weaken (fun _ safe i => (safe i).trans le)⟩

end CallSegments
end PrimalDual
end LinearProgramming
end Optimization
end OAI
