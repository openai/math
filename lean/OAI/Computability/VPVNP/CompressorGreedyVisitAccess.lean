import OAI.Computability.VPVNP.CompressorRecordGreedyInit
import OAI.Computability.VPVNP.CompressorFlowFootprint

/-!
# Addresses accessed by the greedy record reader

Every forbidden operand is fetched in two reads, first from the pointer row
and then from the addressed cell. The search repeats those reads from the
same first pointer. At the end it reads the two header words and writes the
chosen value to the destination named in the header.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SourceTransport

open private fetchOne fetch compareWord compare_run scan pass passes visitHead visitTail from
  OAI.Computability.VPVNP.CompressorRecordGreedy
open private advance_add from OAI.Computability.VPVNP.CompressorRecordGreedyInit

variable {w : ℕ}

private abbrev PointerReads (m : Memory w) (rd : ℕ → Prop) (ptr : Word w) (n : ℕ) :=
  ∀ j < n, rd (advance ptr j).val ∧ rd (m (advance ptr j).val).val

private def AccessRun (s : Word w) (m : Memory w) (rd wr : ℕ → Prop)
    (ops : List (Op 8 0)) (regs out : Regs w 8) : Prop :=
  ∃ es, trace Fin.elim0 s ops regs m = some (es, out, m) ∧ Reads rd es ∧ Writes wr es

private theorem AccessRun.append {s : Word w} {m : Memory w} {rd wr : ℕ → Prop}
    {ops more : List (Op 8 0)} {regs mid out : Regs w 8}
    (left : AccessRun s m rd wr ops regs mid) (right : AccessRun s m rd wr more mid out) :
    AccessRun s m rd wr (ops ++ more) regs out := by
  obtain ⟨es, he, rd₁, wr₁⟩ := left
  obtain ⟨fs, hf, rd₂, wr₂⟩ := right
  exact ⟨es ++ fs, by simp [trace_append, he, hf],
    fun a v h ↦ (List.mem_append.mp h).elim (rd₁ a v) (rd₂ a v),
    fun a v h ↦ (List.mem_append.mp h).elim (wr₁ a v) (wr₂ a v)⟩

private theorem AccessRun.quiet {s : Word w} {m : Memory w} {rd wr : ℕ → Prop}
    {ops : List (Op 8 0)} {regs out : Regs w 8} {es : List (Event w)}
    (run : trace Fin.elim0 s ops regs m = some (es,out,m)) (quiet : countProbes es = 0) :
    AccessRun s m rd wr ops regs out := ⟨es, run, FlowFootprint.bounds_of_noProbes rd wr quiet⟩

private theorem fetch_access (s : Word w) (m : Memory w) (rd wr : ℕ → Prop) (n : ℕ)
    (regs : Regs w 8) (one : regs 1 = 1) (pointers : PointerReads m rd (regs 3) n) :
    ∃ out, AccessRun s m rd wr (fetch n) regs out ∧ out 0 = regs 0 ∧ out 1 = 1 ∧
      out 3 = advance (regs 3) n := by
  induction n generalizing regs with
  | zero => exact ⟨regs, .quiet (es := []) rfl rfl, rfl, one, rfl⟩
  | succ n ih =>
    let ptr := regs 3
    let addr := m ptr.val
    let val := m addr.val
    let xor := BinaryOp.bitXor.eval (regs 4) val
    let mid := Function.update (Function.update (Function.update regs (7 : Fin 8) val) 4 xor) 3 (ptr + 1)
    have head : AccessRun s m rd wr fetchOne regs mid := by
      refine ⟨[.read ptr addr, .read addr val, .tick, .tick], ?_, ?_, ?_⟩
      · simp (config := {decide := true}) [fetchOne, trace, Op.effect, BinaryOp.eval, one,
          mid, ptr, addr, val, xor, Function.update]
      · intro a v h
        simp only [List.mem_cons, List.not_mem_nil, Event.read.injEq, reduceCtorEq, or_false] at h
        rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
        exacts [(pointers 0 (by omega)).1, (pointers 0 (by omega)).2]
      · intro a v h; simp at h
    have rest : PointerReads m rd (mid 3) n := by
      intro j hj
      simpa only [mid, Function.update_self, ptr, advance] using pointers (j+1) (by omega)
    obtain ⟨out, run, h₀, h₁, h₃⟩ := ih mid (by simpa [mid] using one) rest
    exact ⟨out, head.append run, by simpa [mid] using h₀, h₁, by simpa [mid, ptr, advance] using h₃⟩

private theorem scan_access (s : Word w) (m : Memory w) (rd wr : ℕ → Prop) (arity n : ℕ)
    (regs : Regs w 8) (one : regs 1 = 1) (pointers : PointerReads m rd (regs 3) (arity*n)) :
    ∃ out, AccessRun s m rd wr (scan arity n) regs out ∧ out 0 = regs 0 ∧ out 1 = 1 := by
  induction n generalizing regs with
  | zero => exact ⟨regs, .quiet (es := []) rfl rfl, rfl, one⟩
  | succ n ih =>
    let reset := Function.update regs (4 : Fin 8) 0
    have head : AccessRun s m rd wr [.constant 4 0] regs reset := .quiet (es := [.tick]) rfl rfl
    have row : PointerReads m rd (reset 3) arity := by
      intro j hj
      simpa [reset] using pointers j (by rw [Nat.mul_succ]; omega)
    obtain ⟨f, fetchRun, f₀, f₁, f₃⟩ := fetch_access s m rd wr arity reset (by simpa [reset] using one) row
    obtain ⟨c, ⟨es, he, _, noProbes⟩, _, keeps⟩ := compare_run s m f
    have compareRun : AccessRun s m rd wr compareWord f c := .quiet he noProbes
    have next : c 3 = advance (regs 3) arity := by
      simpa [reset] using (keeps 3 (by decide) (by decide)).trans f₃
    have remaining : PointerReads m rd (c 3) (arity*n) := by
      intro j hj
      rw [next, ← advance_add]
      exact pointers _ (by rw [Nat.mul_succ]; omega)
    obtain ⟨out, tail, c₀, c₁⟩ := ih c ((keeps 1 (by decide) (by decide)).trans f₁) remaining
    exact ⟨out, ((head.append fetchRun).append compareRun).append tail,
      by simpa [reset] using c₀.trans ((keeps 0 (by decide) (by decide)).trans f₀), c₁⟩

private theorem pass_access (s : Word w) (m : Memory w) (rd wr : ℕ → Prop) (arity n : ℕ)
    (regs : Regs w 8) (one : regs 1 = 1) (pointers : PointerReads m rd (regs 0) (arity*n)) :
    ∃ out, AccessRun s m rd wr (pass arity n) regs out ∧ out 0 = regs 0 ∧ out 1 = 1 := by
  let reset := Function.update (Function.update regs (3 : Fin 8) (regs 0)) 6 (regs 1)
  have head : AccessRun s m rd wr [.copy 3 0, .copy 6 1] regs reset := by
    apply AccessRun.quiet (es := [.tick, .tick]) _ rfl
    simp [reset, trace, Op.effect]
  obtain ⟨c, scanRun, c₀, c₁⟩ := scan_access s m rd wr arity n reset
    (by simpa [reset] using one) (by simpa [reset] using pointers)
  let diff := c 1 - c 6
  let out := Function.update (Function.update c (6 : Fin 8) diff) 2 (c 2 + diff)
  have tail : AccessRun s m rd wr [.binary .sub 6 1 6, .binary .add 2 2 6] c out := by
    apply AccessRun.quiet (es := [.tick, .tick]) _ rfl
    simp [trace, Op.effect, BinaryOp.eval, diff, out]
  exact ⟨out, (head.append scanRun).append tail, by simpa [out, reset] using c₀,
    by simpa [out] using c₁⟩

private theorem passes_access (s : Word w) (m : Memory w) (rd wr : ℕ → Prop) (arity n j : ℕ)
    (regs : Regs w 8) (one : regs 1 = 1) (pointers : PointerReads m rd (regs 0) (arity*n)) :
    ∃ out, AccessRun s m rd wr (passes arity n j) regs out := by
  induction j generalizing regs with
  | zero => exact ⟨regs, .quiet (es := []) rfl rfl⟩
  | succ j ih =>
    obtain ⟨mid, head, m₀, m₁⟩ := pass_access s m rd wr arity n regs one pointers
    obtain ⟨out, tail⟩ := ih mid m₁ (m₀ ▸ pointers)
    exact ⟨out, head.append tail⟩

/-- Read and write support of the native visitor, including the indirect
operand reads of every search pass. Addresses advance in word arithmetic. -/
theorem visit_access (m : Memory w) (base : Word w) (arity n : ℕ) (rd wr : ℕ → Prop)
    (header : rd base.val) (next : rd (base+1).val)
    (words : ∀ j < arity*n, rd (advance (base+1+1) j).val ∧ rd (m (advance (base+1+1) j).val).val)
    (dest : wr (m base.val).val) (r : Report w)
    (native : execute (visitMachine w arity n).program (1 + (visitCode arity n).length)
      ((visitMachine w arity n).program.start base) m [] = some r) :
    Reads rd r.events ∧ Writes wr r.events := by
  let reset := Function.update (Function.update (Function.update (fun _ : Fin 8 => (0 : Word w)) 0 base) 1 1)
    0 (base+1+1)
  have head : AccessRun base m rd wr visitHead (fun _ ↦ 0) reset := by
    apply AccessRun.quiet (es := [.tick,.tick,.tick,.tick]) _ rfl
    simp (config := {decide := true}) [visitHead, trace, Op.effect, BinaryOp.eval, reset, Function.update]
    rfl
  let start := Function.update (Function.update reset (1 : Fin 8) 1) 2 0
  have init : AccessRun base m rd wr [.constant 1 1,.constant 2 0] reset start :=
    .quiet (es := [.tick,.tick]) rfl rfl
  obtain ⟨c, passesRun⟩ := passes_access base m rd wr arity n n start (by simp [start])
    (by simpa [start, reset] using words)
  obtain ⟨es, he, esRead, esWrite⟩ := head.append (init.append passesRun)
  let addr := m base.val
  let resume := m (base+1).val
  let out := Function.update (Function.update (Function.update (Function.update
    (Function.update c (7 : Fin 8) base) 5 addr) 1 1) 7 (base+1)) 4 resume
  let tail : List (Event w) := [.tick, .read base addr, .tick, .tick, .read (base+1) resume, .write addr (c 2)]
  have ht : trace Fin.elim0 base visitTail c m = some (tail, out, writeMemory m addr (c 2)) := by
    simp (config := {decide := true}) [visitTail, trace, Op.effect, BinaryOp.eval, addr, resume, out,
      tail, Function.update]
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  have full : trace Fin.elim0 base (visitCode arity n) (fun _ ↦ 0) m =
      some (es ++ tail, out, writeMemory m addr (c 2)) := by
    change trace Fin.elim0 base (visitHead ++ choose arity n) (fun _ ↦ 0) m = _ at he
    simp only [visitCode, trace_append, he, ht, Option.bind_some, Option.map_some]
  let M := visitMachine w arity n
  change execute M.program (1 + (visitCode arity n).length) ⟨M.entry, base, fun _ ↦ 0, fun _ ↦ 0⟩ m [] = _ at native
  dsimp only [M, visitMachine] at native
  rw [execute_template, run_eq_trace, full] at native
  have events : es ++ tail = r.events := by simpa using congrArg Report.events (Option.some.inj native)
  rw [← events]
  constructor
  · intro a v h
    rcases List.mem_append.mp h with h | h
    · exact esRead a v h
    · simp only [tail, List.mem_cons, List.not_mem_nil, Event.read.injEq, reduceCtorEq,
        or_false, false_or] at h
      rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
      exacts [header, next]
  · intro a v h
    rcases List.mem_append.mp h with h | h
    · exact esWrite a v h
    · simp only [tail, List.mem_cons, List.not_mem_nil, Event.write.injEq, reduceCtorEq,
        or_false, false_or] at h
      exact h.1 ▸ dest

end CompressorRecords.Greedy

end VPVNP
end Computability
end OAI
