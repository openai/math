import OAI.Optimization.LinearProgramming.RAM.CallableControl
import OAI.Optimization.LinearProgramming.RAM.CallableReturn
import OAI.Optimization.LinearProgramming.Compression.ProxyRelocation

/-! In-place calling convention for a native arithmetic program whose caller
retains data outside the callee's published scratch registers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM RAM.Callable

private def redirect (base table : ℕ) : Instr → Instr
  | .halt tag => .jump (table+2*tag)
  | op => rebaseInstr base op

/-- Every callee instruction retains its physical register operands, and each
return passes through a two-instruction tag table at the end of the fragment. -/
def directCall (callee : Program) (count : ℕ) (sink : TagSink) : Fragment where
  size := callee.length+2*count
  emit base := (callee.map (redirect base (base+callee.length))) ++
    tagTable sink count (base+(callee.length+2*count))
  length_emit _ := by simp

private theorem mapped_fetch {p target : Program} {base table j : ℕ} {op : Instr}
    (code : CodeAt target base (p.map (redirect base table))) (hfetch : p[j]?=some op) :
    target[base+j]?=some (redirect base table op) := by
  obtain ⟨pre,post,rfl,rfl⟩ := code
  have hj : j<p.length := (List.getElem?_eq_some_iff.mp hfetch).choose
  rw [List.append_assoc,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa using hj),List.getElem?_map,hfetch]
  rfl

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem output_eq {op : Instr} {s t : State K} (hn : ∀ b, op≠.halt b)
    (he : execInstr op s=some t) : t.output=s.output := by
  cases op <;> simp only [execInstr] at he
  all_goals try split at he
  all_goals first | contradiction | exact False.elim (hn _ rfl) | (cases he; rfl)

private theorem run_to_table {p target : Program} {base table : ℕ} {P : K → Prop}
    (code : CodeAt target base (p.map (redirect base table)))
    {s t : State K} {k tag : ℕ} (h : Execution p (fun u => ∀ j, P (u.data j)) s k t)
    (live : s.output=none) (done : t.output=some tag) :
    Execution target (fun u => ∀ j, P (u.data j)) (stateAt base s) k
      (t.memory.atPC (table+2*tag)) := by
  induction h with
  | done s _ => rw [live] at done; contradiction
  | @next s u t k hs step rest ih =>
    cases fetch : p[s.pc]? with
    | none => simp [RAM.step,live,fetch] at step
    | some op =>
      have ex : execInstr op s=some u := by simpa [RAM.step,live,fetch] using step
      by_cases stop : ∃ b, op=.halt b
      · obtain ⟨b,rfl⟩ := stop
        have eu : {s with output := some b}=u := Option.some.inj ex
        subst u
        cases rest with
        | done _ hu =>
          have e : b=tag := Option.some.inj done
          subst b
          have start : stateAt base s=s.memory.atPC (base+s.pc) := by
            cases s; simp_all [stateAt,State.memory,Memory.atPC]
          rw [start]
          exact Block.Eval.jump_exec (safe := fun z : Memory K => ∀ j,P (z.data j))
            target _ _ s.memory hs (mapped_fetch code fetch)
        | next _ impossible _ => simp [RAM.step] at impossible
      · have hn : ∀ b, op≠.halt b := fun b e => stop ⟨b,e⟩
        have active := (output_eq hn ex).trans live
        have eq : redirect base table op = rebaseInstr base op := by
          cases op <;> first | rfl | exact False.elim (hn _ rfl)
        have here := mapped_fetch code fetch
        rw [eq] at here
        have machine : RAM.step target (stateAt base s)=some (stateAt base u) := by
          change (match s.output, target[base+s.pc]? with
            | none,some i => execInstr i (stateAt base s)
            | _,_ => none) = _
          rw [live,here]
          exact (exec_rebase base op s).trans (by rw [ex]; rfl)
        exact .next hs machine (ih active done)

/-- Lift the *same* native trace, including its scalar invariant, into any calling
program. The continuation receives the native output banks and the actual tag. -/
theorem directCall_run (p : Program) (count : ℕ) (sink : TagSink) (P : K → Prop) (m : Memory K)
    {k tag : ℕ} {tr : Fin (k+1) → State K} (htag : tag<count) (h : Trace p (m.atPC 0) k tr)
    (safe : ∀ i j,P ((tr i).data j)) (done : (tr (Fin.last k)).output=some tag)
    (hout : ∀ j,P ((sink.store tag (tr (Fin.last k)).memory).data j)) :
    (directCall p count sink).Run P m (k+2) (sink.store tag (tr (Fin.last k)).memory) := by
  intro prog base code
  let table := base+p.length
  let endPC := base+(p.length+2*count)
  have both : CodeAt prog base (p.map (redirect base table) ++ tagTable sink count endPC) := code
  have before := run_to_table both.left (Execution.of_trace h safe) rfl done
  have tableCode : CodeAt prog table (tagTable sink count endPC) := by
    simpa [table] using both.right
  have last := tagTable_exec (safe := fun z : Memory K => ∀ j,P (z.data j))
    sink count endPC table tag (tr (Fin.last k)).memory tableCode htag (safe _) hout
  exact ⟨k+2,le_rfl,by simpa [stateAt,Memory.atPC,endPC,directCall] using before.append last⟩

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI
