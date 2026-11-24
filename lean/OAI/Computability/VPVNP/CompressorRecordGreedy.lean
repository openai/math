import OAI.Computability.VPVNP.PrimedStackRAMCode
import OAI.Computability.VPVNP.RAMRecords
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-!
# Word code for the greedy descriptor choices

A vertex's record contains a fixed number of forbidden expressions. Each
expression is the xor of the words named by its row of pointers. A color
test uses one pointer to the neighbor's current assignment. The tag tests
in Appendix C use the arc displacement, up to two increments, and the
neighbor's current offset. Zero terms can be supplied by a shared zero cell.
The instruction table is fixed once the degree and row arity are fixed.

Starting from candidate zero, each pass increments the candidate exactly
when it occurs among the forbidden expressions. The length of that list
bounds the number of passes needed, including when entries are repeated.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

private abbrev Code := List (Op 8 0)
variable {w : ℕ}

/-- Pointer row traversal, with ordinary word-address arithmetic. -/
def readExpression (m : Memory w) : ℕ → Word w → Word w → Word w × Word w
  | 0, ptr, acc => (ptr, acc)
  | n + 1, ptr, acc => readExpression m n (ptr + 1)
      (BinaryOp.bitXor.eval acc (m (m ptr.val).val))

/-- Values of all forbidden expressions, in descriptor order. -/
def readRows (m : Memory w) (arity : ℕ) : ℕ → Word w → List (Word w)
  | 0, _ => []
  | n + 1, ptr =>
    let (next, value) := readExpression m arity ptr 0
    value :: readRows m arity n next

@[simp] theorem readRows_length (m : Memory w) (arity n : ℕ) (ptr : Word w) :
    (readRows m arity n ptr).length = n := by
  induction n generalizing ptr <;> simp [readRows, *]

private def fetchOne : Code :=
  [.read 7 3, .read 7 7, .binary .bitXor 4 4 7, .binary .add 3 3 1]

private def fetch : ℕ → Code
  | 0 => []
  | n + 1 => fetchOne ++ fetch n

/-- The unsigned quotient of a word by itself tests whether it is nonzero.
The product in register 6 stays one precisely while every comparison differs. -/
private def compareWord : Code :=
  [.binary .sub 5 2 4, .binary .div 5 5 5, .binary .mul 6 6 5]

private def scan (arity : ℕ) : ℕ → Code
  | 0 => []
  | n + 1 => [.constant 4 0] ++ fetch arity ++ compareWord ++ scan arity n

private def pass (arity n : ℕ) : Code :=
  [.copy 3 0, .copy 6 1] ++ scan arity n ++
    [.binary .sub 6 1 6, .binary .add 2 2 6]

private def passes (arity n : ℕ) : ℕ → Code
  | 0 => []
  | j + 1 => pass arity n ++ passes arity n j

/-- Register 0 holds the first descriptor address. The other input registers
may contain arbitrary values. Register 2 returns the least missing index. -/
def choose (arity n : ℕ) : List (Op 8 0) :=
  [.constant 1 1, .constant 2 0] ++ passes arity n n

theorem probes_append (es fs : List (Event w)) :
    countProbes (es ++ fs) = countProbes es + countProbes fs := by
  induction es with
  | nil => simp [countProbes]
  | cons e es ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

private abbrev Run (state : Word w) (m : Memory w) (code : Code)
    (rs out : Regs w 8) (steps probes : ℕ) :=
  ∃ es, trace (Fin.elim0) state code rs m = some (es, out, m) ∧
    es.length = steps ∧ countProbes es = probes

private theorem Run.nil (s : Word w) (m : Memory w) (rs : Regs w 8) :
    Run s m [] rs rs 0 0 := ⟨[], rfl, rfl, rfl⟩

private theorem Run.append {s : Word w} {m : Memory w} {a b : Code}
    {r t u : Regs w 8} {sa sb pa pb : ℕ}
    (ha : Run s m a r t sa pa) (hb : Run s m b t u sb pb) :
    Run s m (a ++ b) r u (sa + sb) (pa + pb) := by
  obtain ⟨es, he, hse, hpe⟩ := ha
  obtain ⟨fs, hf, hsf, hpf⟩ := hb
  refine ⟨es ++ fs, by simp [trace_append, he, hf], by simp [hse, hsf], ?_⟩
  simp [probes_append, hpe, hpf]

private theorem fetch_run (s : Word w) (m : Memory w) (n : ℕ) (rs : Regs w 8)
    (hu : rs 1 = 1) :
    ∃ out, Run s m (fetch n) rs out (4 * n) (2 * n) ∧
      out 3 = (readExpression m n (rs 3) (rs 4)).1 ∧
      out 4 = (readExpression m n (rs 3) (rs 4)).2 ∧
      ∀ i : Fin 8, i ≠ 3 → i ≠ 4 → i ≠ 7 → out i = rs i := by
  induction n generalizing rs with
  | zero => exact ⟨rs, Run.nil s m rs, rfl, rfl, fun _ _ _ _ => rfl⟩
  | succ n ih =>
    let ptr := rs 3
    let addr := m ptr.val
    let val := m addr.val
    let v := BinaryOp.bitXor.eval (rs 4) val
    let mid := Function.update (Function.update (Function.update rs (7 : Fin 8) val) 4 v) 3 (ptr + 1)
    have hmid : Run s m fetchOne rs mid 4 2 := by
      refine ⟨[.read ptr addr, .read addr val, .tick, .tick], ?_, rfl, rfl⟩
      simp (config := { decide := true }) [fetchOne, trace, Op.effect, BinaryOp.eval, hu,
        mid, ptr, addr, val, v, Function.update]
    obtain ⟨out, ho, h3, h4, hk⟩ := ih mid (by simpa [mid] using hu)
    refine ⟨out, ?_, ?_, ?_, fun i a b c => ?_⟩
    · simpa [fetch, Nat.mul_succ, Nat.add_comm] using hmid.append ho
    · simpa [readExpression, mid, ptr, addr, val, v] using h3
    · simpa [readExpression, mid, ptr, addr, val, v] using h4
    · rw [hk i a b c]; simp [mid, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne c]

private theorem quotient_ne (a b : Word w) :
    BinaryOp.div.eval (a - b) (a - b) = if a = b then 0 else 1 := by
  by_cases he : a = b
  · simp [he, BinaryOp.eval]
  · have h : (a - b).val ≠ 0 := by
      intro hz
      exact he (sub_eq_zero.mp (Fin.ext hz))
    simp [BinaryOp.eval, he, Nat.div_self (Nat.pos_of_ne_zero h)]
    rfl

private theorem compare_run (s : Word w) (m : Memory w) (rs : Regs w 8) :
    ∃ out, Run s m compareWord rs out 3 0 ∧
      out 6 = (if rs 2 = rs 4 then 0 else rs 6) ∧
      ∀ i : Fin 8, i ≠ 5 → i ≠ 6 → out i = rs i := by
  let val := BinaryOp.div.eval (rs 2 - rs 4) (rs 2 - rs 4)
  let out := Function.update (Function.update rs (5 : Fin 8) val) 6 (rs 6 * val)
  refine ⟨out, ⟨[.tick, .tick, .tick], ?_, rfl, rfl⟩, ?_, fun i h5 h6 => ?_⟩
  · simp (config := { decide := true }) [trace, Op.effect, compareWord, val, out, BinaryOp.eval,
      Function.update]
  · by_cases h : rs 2 = rs 4 <;> simp [out, val, quotient_ne, h]
  · simp [out, Function.update_of_ne h5, Function.update_of_ne h6]

private theorem scan_run (s : Word w) (m : Memory w) (arity n : ℕ) (rs : Regs w 8)
    (hu : rs 1 = 1) :
    ∃ out, Run s m (scan arity n) rs out ((4 * arity + 4) * n) (2 * arity * n) ∧
      out 6 = (if rs 2 ∈ readRows m arity n (rs 3) then 0 else rs 6) ∧
      ∀ i : Fin 8, i < 3 → out i = rs i := by
  induction n generalizing rs with
  | zero => exact ⟨rs, Run.nil s m rs, by simp [readRows], fun _ _ => rfl⟩
  | succ n ih =>
    let reset := Function.update rs (4 : Fin 8) 0
    have hreset : Run s m [.constant 4 0] rs reset 1 0 := ⟨[.tick], rfl, rfl, rfl⟩
    obtain ⟨f, hf, hp, hv, hfk⟩ := fetch_run s m arity reset (by simpa [reset] using hu)
    have fp : f 3 = (readExpression m arity (rs 3) 0).1 := by simpa [reset] using hp
    have fv : f 4 = (readExpression m arity (rs 3) 0).2 := by simpa [reset] using hv
    have fkeep (i : Fin 8) (h : i < 3 ∨ i = 6) : f i = rs i := by
      have h3 : i ≠ 3 := by omega
      have h4 : i ≠ 4 := by omega
      have h7 : i ≠ 7 := by omega
      rw [hfk i h3 h4 h7]; simp [reset, Function.update_of_ne h4]
    obtain ⟨c, hc, hc6, hck⟩ := compare_run s m f
    have ck (i : Fin 8) (h : i < 3) : c i = rs i :=
      (hck i (by omega) (by omega)).trans (fkeep i (.inl h))
    obtain ⟨out, ho, ho6, hok⟩ := ih c ((ck 1 (by decide)).trans hu)
    refine ⟨out, ?_, ?_, fun i hi => (hok i hi).trans (ck i hi)⟩
    · have h := ((hreset.append hf).append hc).append ho
      convert h using 1 <;> first | rfl | ring
    · rw [ho6, hc6, ck 2 (by decide), hck 3 (by decide) (by decide), fp,
        fkeep 2 (.inl (by decide)), fkeep 6 (.inr rfl), fv]
      simp only [readRows, List.mem_cons]
      split_ifs <;> simp_all

/-- Successive candidates produced by the fixed number of complete row passes. -/
def climb (forbidden : List ℕ) : ℕ → ℕ → ℕ
  | 0, start => start
  | steps + 1, start =>
    climb forbidden steps (if start ∈ forbidden then start + 1 else start)

theorem climb_to_missing {xs : List ℕ} {target : ℕ} (absent : target ∉ xs)
    (earlier : ∀ i < target, i ∈ xs) (steps start : ℕ) (hs : start ≤ target)
    (enough : target ≤ start + steps) : climb xs steps start = target := by
  induction steps generalizing start with
  | zero => simp [climb]; omega
  | succ steps ih =>
    by_cases he : start = target
    · subst start; simp [climb, absent, ih target le_rfl (by omega)]
    · have hl : start < target := by omega
      simp [climb, earlier _ hl, ih (start + 1) (by omega) (by omega)]


private theorem pass_run (s : Word w) (m : Memory w) (arity n : ℕ) (rs : Regs w 8)
    (hu : rs 1 = 1) :
    ∃ out, Run s m (pass arity n) rs out ((4 * arity + 4) * n + 4) (2 * arity * n) ∧
      out 2 = (if rs 2 ∈ readRows m arity n (rs 0) then rs 2 + 1 else rs 2) ∧
      out 0 = rs 0 ∧ out 1 = rs 1 := by
  let reset := Function.update (Function.update rs (3 : Fin 8) (rs 0)) 6 (rs 1)
  have hr : Run s m [.copy 3 0, .copy 6 1] rs reset 2 0 := by
    refine ⟨[.tick, .tick], ?_, rfl, rfl⟩
    simp [trace, Op.effect, reset]
  obtain ⟨c, hc, h6, hk⟩ := scan_run s m arity n reset (by simpa [reset] using hu)
  have keep (i : Fin 8) (hi : i < 3) : c i = rs i := by
    rw [hk i hi]; simp [reset, Function.update_of_ne (show i ≠ 3 by omega),
      Function.update_of_ne (show i ≠ 6 by omega)]
  have hflag : c 6 = if rs 2 ∈ readRows m arity n (rs 0) then 0 else 1 := by
    simpa [reset, hu] using h6
  let diff := c 1 - c 6
  let out := Function.update (Function.update c (6 : Fin 8) diff) 2 (c 2 + diff)
  have ht : Run s m [.binary .sub 6 1 6, .binary .add 2 2 6] c out 2 0 := by
    refine ⟨[.tick, .tick], ?_, rfl, rfl⟩
    simp [trace, Op.effect, out, diff, BinaryOp.eval]
  refine ⟨out, ?_, ?_, ?_, ?_⟩
  · convert (hr.append hc).append ht using 1 <;> first | rfl | omega
  · by_cases h : rs 2 ∈ readRows m arity n (rs 0) <;>
      simp [out, diff, hflag, keep 1 (by decide), keep 2 (by decide), hu, h]
  · simpa [out] using keep 0 (by decide)
  · simpa [out] using keep 1 (by decide)

private theorem mem_values (x : Word w) (xs : List (Word w)) :
    x.val ∈ xs.map Fin.val ↔ x ∈ xs  := by
  constructor
  · intro h
    obtain ⟨y, hy, hval⟩ := List.mem_map.mp h
    rwa [← Fin.ext hval]
  · exact List.mem_map_of_mem

private theorem passes_run (s : Word w) (m : Memory w) (arity n j : ℕ) (rs : Regs w 8)
    (hu : rs 1 = 1) (hfit : (rs 2).val + j < 2 ^ w) :
    ∃ out, Run s m (passes arity n j) rs out (((4 * arity + 4) * n + 4) * j)
      (2 * arity * n * j) ∧
      (out 2).val = climb ((readRows m arity n (rs 0)).map Fin.val) j (rs 2).val := by
  induction j generalizing rs with
  | zero => exact ⟨rs, Run.nil s m rs, rfl⟩
  | succ j ih =>
    obtain ⟨c, hc, h2, h0, h1⟩ := pass_run s m arity n rs hu
    have hv : (c 2).val = if (rs 2).val ∈ (readRows m arity n (rs 0)).map Fin.val
        then (rs 2).val + 1 else (rs 2).val := by
      simp only [mem_values, h2]
      split_ifs with h
      · have hone : (1 : Word w).val = 1 := by
          rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
        rw [Fin.val_add, hone, Nat.mod_eq_of_lt (by omega)]
      · rfl
    have hfit' : (c 2).val + j < 2 ^ w := by rw [hv]; split <;> omega
    obtain ⟨out, ho, hval⟩ := ih c (h1.trans hu) hfit'
    refine ⟨out, ?_, ?_⟩
    · simpa [passes, Nat.mul_succ, Nat.add_comm] using hc.append ho
    · rw [hval, h0, hv, climb]

/-- The block reads from the descriptor address in register zero. The stated
event counts include all row dereferences, even for a repeated forbidden word. -/
theorem choose_trace (s : Word w) (m : Memory w) (arity n : ℕ) (rs : Regs w 8)
    (hfit : n < 2 ^ w) :
    ∃ es out, trace Fin.elim0 s (choose arity n) rs m = some (es, out, m) ∧
      es.length = 2 + ((4 * arity + 4) * n + 4) * n ∧
      countProbes es = 2 * arity * n * n ∧
      (out 2).val = climb ((readRows m arity n (rs 0)).map Fin.val) n 0 := by
  let init := Function.update (Function.update rs (1 : Fin 8) 1) 2 0
  have hi : Run s m [.constant 1 1, .constant 2 0] rs init 2 0 := ⟨[.tick, .tick], rfl, rfl, rfl⟩
  obtain ⟨out, ho, hv⟩ := passes_run s m arity n n init (by simp [init]) (by simpa [init] using hfit)
  obtain ⟨es, he, hl, hp⟩ := hi.append ho
  exact ⟨es, out, he, hl, by simpa using hp, by simpa [init] using hv⟩

/-- Starting a fresh burst call uses the persistent input as the row address. -/
def chooseFromState (arity n : ℕ) : List (Op 8 0) :=
  [.stateWord 0] ++ choose arity n

/-- Native execution from freshly reset private memory and registers. The candidate
returned in the persistent state is the least omitted nonnegative index. -/
theorem choose_native (m : Memory w) (base : Word w) (arity n target : ℕ)
    (hfit : n < 2 ^ w) (absent : target ∉ (readRows m arity n base).map Fin.val)
    (earlier : ∀ i < target, i ∈ (readRows m arity n base).map Fin.val) :
    let code := chooseFromState arity n
    let M := (template code 2).instantiate w Fin.elim0
    ∃ es, execute M.program (1 + code.length) (M.program.start base) m [] =
        some ⟨es, some (Fin.ofNat _ target)⟩ ∧
      es.length = 3 + ((4 * arity + 4) * n + 4) * n ∧ countProbes es = 2 * arity * n * n := by
  dsimp only
  let rs : Regs w 8 := Function.update (fun _ => 0) 0 base
  have hbase : rs 0 = base := by simp [rs]
  have hn : target ≤ n := by
    have hsub : List.range target ⊆ (readRows m arity n base).map Fin.val := by
      intro i hi; exact earlier _ (List.mem_range.mp hi)
    simpa using List.nodup_range.length_le_of_subset hsub
  obtain ⟨es, out, he, hl, hp, hv⟩ := choose_trace base m arity n rs hfit
  rw [hbase, climb_to_missing absent earlier n 0 (Nat.zero_le _) (by omega)] at hv
  have result : out 2 = Fin.ofNat _ target :=
    Fin.ext (hv.trans (Nat.mod_eq_of_lt (hn.trans_lt hfit)).symm)
  have init : trace Fin.elim0 base [.stateWord 0] (fun _ : Fin 8 => 0) m =
      some ([.tick], rs, m) := rfl
  refine ⟨.tick :: es, ?_, by simp [hl]; omega, hp⟩
  let M := (template (chooseFromState arity n) 2).instantiate w Fin.elim0
  change execute M.program (1 + (chooseFromState arity n).length)
    ⟨M.entry, base, fun _ => 0, fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, chooseFromState, trace_append, init]
  simp [he, result]


/-- A visitor's header contains the label destination and the next vertex's
header address. The forbidden operand rows immediately follow that header. -/
private def visitHead : Code :=
  [.stateWord 0, .constant 1 1, .binary .add 0 0 1, .binary .add 0 0 1]

private def visitTail : Code :=
  [.stateWord 7, .read 5 7, .constant 1 1, .binary .add 7 7 1, .read 4 7, .write 5 2]

/-- Instructions for one greedy vertex visit, loading its record, choosing a label that passes
the forbidden-expression tests, and advancing the cursor. -/
def visitCode (arity n : ℕ) : List (Op 8 0) := visitHead ++ choose arity n ++ visitTail

/-- Instantiate the greedy visit at the specified word width with register four as its return
register and no public operands. -/
def visitMachine (w arity n : ℕ) := (template (visitCode arity n) 4).instantiate w Fin.elim0

/-- Observable execution of one complete vertex visit. The output label is
stored externally and the persistent return word is the next record address. -/
def Visit (m : Memory w) (base : Word w) (arity n : ℕ) (v : Word w) : Prop :=
  let P := (visitMachine w arity n).program
  ∃ es, execute P (1 + (visitCode arity n).length) (P.start base) m [] =
      some ⟨es, some (m (base + 1).val)⟩ ∧
    after m es = writeMemory m (m base.val) v ∧
    es.length = 12 + ((4 * arity + 4) * n + 4) * n ∧
    countProbes es = 3 + 2 * arity * n * n

private theorem effect_memory {k r : ℕ} {op : Op r k} {pub : Fin k → Word w} {s : Word w}
    {rs out : Regs w r} {m final : Memory w} {e : Event w}
    (he : op.effect pub s rs m = some (e, out, final)) : update m e = final := by
  cases op <;> simp only [Op.effect, Option.some.injEq, Prod.mk.injEq] at he
  all_goals first
    | obtain ⟨rfl, rfl, rfl⟩ := he; rfl
    | split at he <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at he
  all_goals obtain ⟨rfl, rfl, rfl⟩ := he; rfl

theorem trace_after {k r : ℕ} {pub : Fin k → Word w} {s : Word w}
    {ops : List (Op r k)} {rs out : Regs w r} {m final : Memory w} {es : List (Event w)}
    (h : trace pub s ops rs m = some (es, out, final)) : after m es = final := by
  induction ops generalizing rs m es with
  | nil => simp [trace] at h; rw [h.1, h.2.2]; rfl
  | cons op ops ih =>
    cases he : op.effect pub s rs m with
    | none => simp [trace, he] at h
    | some t =>
      obtain ⟨e, rs', m'⟩ := t
      cases ht : trace pub s ops rs' m' with
      | none => simp [trace, he, ht] at h
      | some u =>
        obtain ⟨fs, rs'', m''⟩ := u
        simp [trace, he, ht] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        change after (update m e) fs = m''
        rw [effect_memory he]
        exact ih ht

theorem visit_native (m : Memory w) (base v : Word w) (arity n : ℕ) (hfit : n < 2 ^ w)
    (hvalue : climb ((readRows m arity n (base + 1 + 1)).map Fin.val) n 0 = v.val) :
    Visit m base arity n v := by
  let init : Regs w 8 := Function.update (Function.update (Function.update (fun _ => 0) (0 : Fin 8) base) 1 1) 0 (base + 1 + 1)
  have hhead : trace Fin.elim0 base visitHead (fun _ : Fin 8 => 0) m =
      some ([.tick, .tick, .tick, .tick], init, m) := by
    simp (config := {decide := true}) [visitHead, trace, Op.effect, BinaryOp.eval, init, Function.update]
    rfl
  obtain ⟨es, c, hc, hl, hp, hv⟩ := choose_trace base m arity n init hfit
  have cv : c 2 = v := Fin.ext (by simpa [init, hvalue] using hv)
  let a := m base.val
  let next := m (base + 1).val
  let tailEvents : List (Event w) := [.tick, .read base a, .tick, .tick, .read (base + 1) next, .write a v]
  let out := Function.update (Function.update (Function.update (Function.update (Function.update c (7 : Fin 8) base) 5 a)
    1 1) 7 (base + 1)) 4 next
  let final := writeMemory m a v
  have ht : trace Fin.elim0 base visitTail c m = some (tailEvents, out, final) := by
    simp (config := {decide := true}) [visitTail, trace, Op.effect, BinaryOp.eval, a, next, tailEvents, cv,
      out, final, Function.update]
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  let events := ([.tick, .tick, .tick, .tick] ++ es) ++ tailEvents
  have he : trace Fin.elim0 base (visitCode arity n) (fun _ : Fin 8 => 0) m = some (events, out, final) := by
    simp [visitCode, trace_append, hhead, hc, ht, events]
  refine ⟨events, ?_, trace_after he, ?_, ?_⟩
  · let M := visitMachine w arity n
    change execute M.program (1 + (visitCode arity n).length)
      ⟨M.entry, base, fun _ => 0, fun _ => 0⟩ m [] = _
    dsimp only [M, visitMachine]
    rw [execute_template, run_eq_trace, he]
    simp [out, next]
  · simp [events, tailEvents, hl]; omega
  · simp [events, probes_append, tailEvents, countProbes, hp]; omega

end CompressorRecords.Greedy

end VPVNP
end Computability
end OAI
