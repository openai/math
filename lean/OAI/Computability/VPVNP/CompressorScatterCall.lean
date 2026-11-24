import OAI.Computability.VPVNP.CompressorRecordsRowRecipe

/-!
# A native call with a bank of scattered stores

A finite list of assignments snapshots every operand from the entry memory.
The call then stores selected registers to computed addresses and returns
one designated register. The exact external effect is a fold of these stores.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScatterCall

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM RowRecipe
open private eval_cost from OAI.Computability.VPVNP.CompressorRecordsRowRecipe

variable {w r k : ℕ}

/-- Translate a row-recipe register assignment to its corresponding burst operation. -/
def op (a : Assign r k) : Op r k := match a.rhs with
  | .literal v => .constant a.dst v
  | .publicWord i => .publicWord a.dst i
  | .state => .stateWord a.dst
  | .copy i => .copy a.dst i
  | .binary f i j => .binary f a.dst i j
  | .read i => .read a.dst i

/-- Run all register assignments, then emit the ordered external writes from the selected
register pairs. -/
def ops (code : List (Assign r k)) (writes : List (Fin r × Fin r)) : List (Op r k) :=
  code.map op ++ writes.map (fun (i,j) => .write i j)

/-- Resolve address and value register pairs to a list of word-addressed stores. -/
def stores (rs : Regs w r) (writes : List (Fin r × Fin r)) :=
  writes.map (fun (i,j) => (rs i,rs j))

/-- Encode the ordered address-value pairs as external write events. -/
def storeLog (xs : List (Word w × Word w)) : List (Event w) := xs.map (fun (a,v) => .write a v)

/-- Apply the ordered stores to memory, with later writes taking precedence at a repeated
address. -/
def applyStores (mem : Memory w) (xs : List (Word w × Word w)) :=
  xs.foldl (fun m av => writeMemory m av.1 av.2) mem

private theorem assignments (xs : List (Assign r k)) (pub : Fin k → Word w) (st : Word w)
    (m : Memory w) (rs : Regs w r) :
    let out := evaluate pub st m xs rs
    trace pub st (xs.map op) rs m = some (out.1,out.2,m) := by
  induction xs generalizing rs with
  | nil => rfl
  | cons a as ih =>
    have effect : (op a).effect pub st rs m = some (a.rhs.event m rs,
        Function.update rs a.dst (a.rhs.value pub st m rs),m) := by
      cases a with | mk dst rhs => cases rhs <;> rfl
    simp only [List.map_cons,trace,effect,bind,Option.bind_some,ih,evaluate]; rfl

private theorem writing (xs : List (Fin r × Fin r)) (pub : Fin k → Word w) (st : Word w)
    (m : Memory w) (rs : Regs w r) :
    trace pub st (xs.map (fun (i,j) => .write i j)) rs m =
      some (storeLog (stores rs xs),rs,applyStores m (stores rs xs)) := by
  induction xs generalizing m with
  | nil => rfl
  | cons av xs ih =>
    cases av
    simp [trace,Op.effect,ih,stores,storeLog,applyStores]

/-- Evaluate the assignments from zero registers, append the selected stores to the event log,
and return the designated register's value. -/
def report (xs : List (Assign r k)) (writes : List (Fin r × Fin r)) (ret : Fin r) (pub : Fin k → Word w)
    (st : Word w) (m : Memory w) : Report w :=
  let out := evaluate pub st m xs (fun _ => 0)
  ⟨out.1 ++ storeLog (stores out.2 writes),some (out.2 ret)⟩

private theorem trace_call (xs : List (Assign r k)) (writes : List (Fin r × Fin r)) (ret : Fin r)
    (pub : Fin k → Word w) (st : Word w) (m : Memory w) :
    let out := evaluate pub st m xs (fun _ => 0)
    trace pub st (ops xs writes) (fun _ => 0) m = some
      ((report xs writes ret pub st m).events,out.2,applyStores m (stores out.2 writes)) := by
  rw [ops,trace_append,assignments]; simp only [Option.bind_some,writing]; rfl

theorem native (xs : List (Assign r k)) (writes : List (Fin r × Fin r)) (ret : Fin r)
    (pub : Fin k → Word w) (st : Word w) (m : Memory w) :
    let T := ((template (ops xs writes) ret).instantiate w pub).program
    execute T (1+(ops xs writes).length) (T.start st) m [] = some (report xs writes ret pub st m) := by
  let T := (template (ops xs writes) ret).instantiate w pub
  change execute T.program (1+(ops xs writes).length) ⟨T.entry,st,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template,run_eq_trace,trace_call xs writes ret]; simp [report]

theorem effect (xs : List (Assign r k)) (writes : List (Fin r × Fin r)) (ret : Fin r)
    (pub : Fin k → Word w) (st : Word w) (m : Memory w) :
    after m (report xs writes ret pub st m).events =
      applyStores m (stores (evaluate pub st m xs (fun _ => 0)).2 writes) :=
  Greedy.trace_after (trace_call xs writes ret pub st m)

theorem cost (xs : List (Assign r k)) (writes : List (Fin r × Fin r)) (ret : Fin r)
    (pub : Fin k → Word w) (st : Word w) (m : Memory w) :
    let rep := report xs writes ret pub st m
    rep.events.length = xs.length+writes.length ∧ rep.probes = (xs.map fun a => a.rhs.reads).sum + writes.length ∧
      choiceBits rep.events = [] := by
  dsimp only
  have e := eval_cost pub st m xs (fun _ => 0)
  have sl (vs : List (Word w × Word w)) : countProbes (storeLog vs) = vs.length := by
    induction vs with | nil => rfl | cons x xs ih => simpa only [storeLog,List.map_cons,countProbes,List.length_cons,Nat.add_comm 1] using congrArg Nat.succ ih
  refine ⟨by simp [report,storeLog,stores,e.1],?_,(execute_spec (native xs writes ret pub st m)).2.2⟩
  change countProbes (_ ++ storeLog _) = _
  rw [Greedy.probes_append,e.2,sl]; simp [stores]

theorem outside (xs : List (Word w × Word w)) (m : Memory w) (x : ℕ)
    (h : ∀ av ∈ xs, av.1.val ≠ x) : applyStores m xs x = m x := by
  induction xs generalizing m with
  | nil => rfl
  | cons av xs ih =>
    change applyStores (writeMemory m av.1 av.2) xs x = _
    rw [ih _ (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    exact ite_eq_right (h av List.mem_cons_self).symm

theorem stored (xs : List (Word w × Word w)) (m : Memory w) {x : ℕ} {v : Word w}
    (live : ∃ av ∈ xs, av.1.val = x) (agree : ∀ av ∈ xs, av.1.val = x → av.2 = v) :
    applyStores m xs x = v := by
  induction xs generalizing m with
  | nil => simp at live
  | cons av xs ih =>
    change applyStores (writeMemory m av.1 av.2) xs x = _
    by_cases h : ∃ u ∈ xs, u.1.val = x
    · exact ih _ h (fun u hu => agree u (List.mem_cons_of_mem _ hu))
    · rw [outside _ _ _ (fun u hu he => h ⟨u,hu,he⟩)]
      have ha : av.1.val = x := by
        obtain ⟨u,hu,he⟩ := live
        rcases List.mem_cons.mp hu with rfl | hu
        · exact he
        · exact (h ⟨u,hu,he⟩).elim
      simp [writeMemory,ha,agree av List.mem_cons_self ha]

end CompressorRecords.ScatterCall

end VPVNP
end Computability
end OAI
