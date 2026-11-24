import OAI.Computability.VPVNP.LiveEvaluatorRAMPrepare
import OAI.Computability.VPVNP.PrimedCounterCall
import OAI.Computability.VPVNP.PrimedInputRAMOnce
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-!
# Scheduled burst calls for one live evaluator transition

Cursor zero selects the transition and saves its five fields in external
scratch. The following calls check one cell of the first tape and then one
cell of the second tape. All four public words are lengths or addresses.
The instruction table is independent of the radius, word width and addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAM.Schedule

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM

/-- A native block for the scheduled transition checker with four public operands. -/
abbrev Block := LiveEvaluatorRAM.Code 4
/-- The operand indices for window radius, old configuration, proposed configuration, and
instruction scratch. -/
abbrev Pub := Fin 4
/-- A single scheduled transition-checker operation over its 32 registers and four public
operands. -/
abbrev Op := PrimedStackRAM.Op 32 4

variable {w : ℕ}

/-- Sequence of one or more elementary opcodes in their indicated order. -/
private def ops (a : Op) (rest : List Op) : Block :=
  PrimedStackRAM.straight a rest

/-- Public words are radius, old configuration base, new configuration base,
and the base of five scratch words. The old state is read once per call. -/
def load : Block := ops (.constant 0 0)
  [.constant 1 1, .constant 2 2, .constant 3 3, .publicWord 11 0, .binary .add 12 11 11,
   .binary .add 22 12 1, .publicWord 23 1, .publicWord 24 2, .publicWord 25 3,
   .stateWord 26, .read 16 23]

/-- Select the first tape and its first write/move pair in scratch. -/
private def first : Block := ops (.binary .add 14 23 1)
  [.binary .add 15 24 1, .binary .add 20 25 1]

/-- Select the second tape, subtract the first tape length from the old cell
index, and select its second write/move pair in scratch. -/
private def second : Block := ops (.binary .sub 13 13 22)
  [.binary .add 14 23 1, .binary .add 14 14 22, .binary .add 15 24 1,
   .binary .add 15 15 22, .binary .add 20 25 3]

/-- Read the target state and the write/move pair of the scheduled tape. -/
def locate : Block :=
  .seq (ops (.binary .sub 13 26 1) [.read 5 25])
    (.seq (.ifLt 13 22 first second)
      (ops (.read 6 20) [.binary .add 20 20 1, .read 7 20]))

/-- Compute the next cursor and total number of calls afresh after checking
the cell. This also works after the first call's transition dispatch. -/
def finish : Block := ops (.stateWord 29)
  [.constant 1 1, .binary .add 29 29 1, .publicWord 30 0, .binary .add 30 30 30,
   .binary .add 30 30 1, .binary .add 30 30 30, .binary .add 30 30 1]

/-- At cursor zero prepare a transition, otherwise locate and check the indexed tape cell, then
compute the return cursor. -/
def body (prepare : Block) : Block :=
  .seq load (.seq (.ifEq 26 0 prepare (.seq locate cell)) finish)

/-- The burst-call template for the transition schedule with its supplied
instruction-preparation block. -/
def table (prepare : Block) := PrimedCounter.Call.template (body prepare) 29 30

/-- One dispatch, followed by a visit to every cell in each tape window. -/
def calls (M : ℕ) := 1 + 2 * (2 * M + 1)

/-- Whether a cell-check ordinal belongs to the first tape's window. -/
def isFirst {M : ℕ} (i : Fin (2 * (2 * M + 1))) := i.val < 2 * M + 1

/-- The scheduled visits form a bijection between the two tape fields and
the noninitial calls, in tape order and increasing cell order. -/
def visit (M : ℕ) : (Fin 2 × Fin (2 * M + 1)) ≃ Fin (2 * (2 * M + 1)) := finProdFinEquiv

@[simp] theorem visit_first {M : ℕ} (j : Fin (2 * M + 1)) :
    (visit M (0, j)).val = j.val := by simp [visit, finProdFinEquiv]

@[simp] theorem visit_second {M : ℕ} (j : Fin (2 * M + 1)) :
    (visit M (1, j)).val = j.val + (2 * M + 1) := by simp [visit, finProdFinEquiv]

/-- Apply an ordered list of word assignments to the evaluator register bank. -/
def install (rs : Regs w 32) (fields : List (Reg × Word w)) : Regs w 32 :=
  fields.foldl (fun r x => Function.update r x.1 x.2) rs

/-- The register bank after loading the radius, configuration and scratch addresses, persistent
cursor, and old control word. -/
def loaded (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) (m : Memory w) : Regs w 32 :=
  let M := pub 0
  install rs [(0, 0), (1, 1), (2, 2), (3, 3), (11, M), (12, M + M), (22, M + M + 1),
    (23, pub 1), (24, pub 2), (25, pub 3), (26, state), (16, m (pub 1).val)]

/-- A complete register-bank witness and event trace for the common prefix. -/
theorem load_exec (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) (m : Memory w) :
    Flow.Exec pub state load rs m
      (List.replicate 11 .tick ++ [.read (pub 1) (m (pub 1).val)]) (loaded pub state rs m) m :=
  (Flow.once_sound pub state false load rs m rfl).1

/-- Selected tape index, bases, target, write symbol and move after three
reads from the five words saved by the preparation call. -/
def located (rs : Regs w 32) (m : Memory w) : Regs w 32 :=
  let i := rs 26 - rs 1
  let a := install rs [(13, i), (5, m (rs 25).val)]
  let b := if i < rs 22 then
      install a [(14, rs 23 + rs 1), (15, rs 24 + rs 1), (20, rs 25 + rs 1)]
    else
      install a [(13, i - rs 22), (14, rs 23 + rs 1), (14, rs 23 + rs 1 + rs 22),
        (15, rs 24 + rs 1), (15, rs 24 + rs 1 + rs 22), (20, rs 25 + rs 3)]
  let addr := if i < rs 22 then rs 25 + rs 1 else rs 25 + rs 3
  install b [(6, m addr.val), (20, addr + rs 1), (7, m (addr + rs 1).val)]

/-- The read of the selected target and the reads of the write symbol and motion for the tape
chosen by the cursor. -/
def locateEvents (rs : Regs w 32) (m : Memory w) : List (Event w) :=
  let f := rs 26 - rs 1 < rs 22
  let addr := if f then rs 25 + rs 1 else rs 25 + rs 3
  [.tick, .read (rs 25) (m (rs 25).val), .tick] ++ List.replicate (if f then 3 else 6) .tick ++
    [.read addr (m addr.val), .tick, .read (addr + rs 1) (m (addr + rs 1).val)]

theorem locate_exec (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) (m : Memory w) :
    Flow.Exec pub state locate rs m (locateEvents rs m) (located rs m) m := by
  apply (Flow.once_sound pub state false locate rs m ?_).1
  by_cases h : rs 26 - rs 1 < rs 22
  all_goals simp only [locateEvents, located, h, ↓reduceIte]
  all_goals
    simp (config := { decide := true }) [locate, ops, PrimedStackRAM.straight, Flow.once, Op.effect, BinaryOp.eval, pure, bind, h]
    rfl

/-- Closing register bank has successor cursor and total call count. -/
def finished (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) : Regs w 32 :=
  let M := pub 0
  let last := M + M
  let width := last + 1
  install rs [(29, state), (1, 1), (29, state + 1), (30, M), (30, last), (30, width),
    (30, width + width), (30, width + width + 1)]

theorem finish_exec (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) (m : Memory w) :
    Flow.Exec pub state finish rs m (List.replicate 8 .tick) (finished pub state rs) m :=
  (Flow.once_sound pub state false finish rs m rfl).1

theorem finish_next (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) :
    finished pub state rs 29 = state + 1 := rfl

open scoped Fin.CommRing in
theorem finish_total (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) :
    finished pub state rs 30 = (calls (pub 0).val : Word w) := by
  change (pub 0 + pub 0 + 1) + (pub 0 + pub 0 + 1) + 1 = _
  simp only [calls, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Fin.cast_val_eq_self]
  ring

theorem body_loopFree (prepare : Block) (h : loopFree prepare = true) :
    loopFree (body prepare) = true := by
  change (true && ((loopFree prepare && true) && true)) = true
  simp [h]

/-- Actual word program for every scheduled call of a fixed evaluator. -/
def program (p : UniversalMachine.Program) := table (LiveEvaluatorRAMPrepare.prepare p)

theorem program_bound (p : UniversalMachine.Program) {pub : Pub → Word w} {state : Word w}
    {rs m es out mem} (run : Flow.Exec pub state (body (LiveEvaluatorRAMPrepare.prepare p)) rs m es out mem) :
    es.length ≤ (body (LiveEvaluatorRAMPrepare.prepare p)).length :=
  length_le_of_loopFree run (body_loopFree _ (LiveEvaluatorRAMPrepare.prepare_loopFree p))

private def deterministic : Block → Bool
  | .line _ => true
  | .seq a b | .ifEq _ _ a b | .ifLt _ _ a b => deterministic a && deterministic b
  | .branch .. | .whileLt .. => false

private theorem once_of_exec {pub : Pub → Word w} {st : Word w} {a : Block} {rs m es out mem}
    (run : Flow.Exec pub st a rs m es out mem) (h : deterministic a = true) :
    Flow.once pub st false a rs m = some (es, out, mem) := by
  induction run with
  | line he => simp [Flow.once, he]
  | seq _ _ ia ib =>
    simp only [deterministic, Bool.and_eq_true] at h
    simp [Flow.once, ia h.1, ib h.2]
  | ifEqYes ht _ ih | ifLtYes ht _ ih =>
    simp only [deterministic, Bool.and_eq_true] at h
    simp only [Flow.once, ht, ite_true, ih h.1, Option.map_some]
    rfl
  | ifEqNo ht _ ih | ifLtNo ht _ ih =>
    simp only [deterministic, Bool.and_eq_true] at h
    simp only [Flow.once, ht, ite_false, ih h.2, Option.map_some]
    rfl
  | branchYes | branchNo | whileDone | whileStep => contradiction

private theorem unique_exec {pub : Pub → Word w} {st : Word w} {a : Block} {rs m es out mem fs r' m'}
    (ha : deterministic a = true) (x : Flow.Exec pub st a rs m es out mem)
    (y : Flow.Exec pub st a rs m fs r' m') :
    es = fs ∧ out = r' ∧ mem = m' := by
  simpa using (once_of_exec x ha).symm.trans (once_of_exec y ha)

private theorem exits_unique {pub : Pub → Word w} {st : Word w} {a : Block} {rs m es out mem}
    (ha : deterministic a = true) (run : Flow.Exec pub st a rs m es out mem)
    (post : Regs w 32 → Memory w → Prop) :
    exits pub st a rs m post ↔ post out mem := by
  constructor
  · rintro ⟨_, _, _, hy, hp⟩
    obtain ⟨rfl, rfl, rfl⟩ := unique_exec ha run hy
    exact hp
  · exact fun hp => ⟨_, _, _, run, hp⟩

/-- At cursor zero the body executes preparation. At all other cursors it
checks exactly the addressed cell. Both phases compute the successor cursor
in the same final fragment. This equivalence holds on arbitrary memory. -/
theorem body_exits (p : UniversalMachine.Program) (pub : Pub → Word w) (st : Word w)
    (rs : Regs w 32) (m : Memory w) (post : Regs w 32 → Memory w → Prop) :
    let pre := loaded pub st rs m
    let close := fun out mem => post (finished pub st out) mem
    exits pub st (body (LiveEvaluatorRAMPrepare.prepare p)) rs m post ↔
      if st = 0 then exits pub st (LiveEvaluatorRAMPrepare.prepare p) pre m close
      else exits pub st cell (located pre m) m close := by
  dsimp only
  rw [body, exits_seq, exits_unique (by rfl) (load_exec ..), exits_seq, exits_ifEq]
  have h (a : Block) (r : Regs w 32) (u : Memory w) :
      exits pub st a r u (fun r' u' => exits pub st finish r' u' post) ↔
        exits pub st a r u (fun r' u' => post (finished pub st r') u') := by
    have e (r' : Regs w 32) (u' : Memory w) :=
      exits_unique (by rfl) (finish_exec pub st r' u') post
    have heq : (fun r' u' => exits pub st finish r' u' post) =
        (fun r' u' => post (finished pub st r') u') := funext fun r' => funext fun u' => propext (e r' u')
    rw [heq]
  change (if st = 0 then _ else _) ↔ _
  split
  · exact h ..
  · rw [exits_seq, exits_unique (by rfl) (locate_exec ..), h]

theorem noninitial_call_iff (p : UniversalMachine.Program) (pub : Pub → Word w) {st : Word w}
    (hs : st ≠ 0) (rs : Regs w 32) (m : Memory w) :
    (∃ es out mem, Flow.Exec pub st (body (LiveEvaluatorRAMPrepare.prepare p)) rs m es out mem) ↔
      cellTest (located (loaded pub st rs m) m) m := by
  have he := body_exits p pub st rs m (fun _ _ => True)
  simpa only [ite_eq_right hs, exits, and_true, cell_exec_iff] using he

/-- Every normal exit publishes the successor and the total, including a
branch of the preparation call that changes external scratch memory. -/
theorem body_cursor {p : UniversalMachine.Program} {pub : Pub → Word w} {st : Word w}
    {rs m es out mem} (run : Flow.Exec pub st (body (LiveEvaluatorRAMPrepare.prepare p)) rs m es out mem) :
    out 29 = st + 1 ∧ out 30 = Fin.ofNat (2 ^ w) (calls (pub 0).val) := by
  cases run with
  | seq _ tail =>
    cases tail with
    | seq _ close =>
      obtain ⟨_, rfl, _⟩ := unique_exec (by rfl) close (finish_exec ..)
      exact ⟨finish_next .., finish_total ..⟩

/-- Exact native report, with surplus choice bits rejected at the common
exit. Only the final cell accepts instead of returning another cursor. -/
theorem execute_call {p : UniversalMachine.Program} {pub : Pub → Word w} {st : Word w}
    {rs m es out mem} (run : Flow.Exec pub st (body (LiveEvaluatorRAMPrepare.prepare p)) rs m es out mem)
    (privateMem : Word w → Word w) (extra : List Bool) (fuel : ℕ) :
    let machine := (program p).instantiate w pub
    execute machine.program (es.length + (fuel + 2)) ⟨machine.entry, st, rs, privateMem⟩ m
      (choiceBits es ++ extra) =
      if extra.isEmpty then some ⟨es ++ [.tick],
        if st + 1 = Fin.ofNat (2 ^ w) (calls (pub 0).val) then none else some (st + 1)⟩ else none := by
  obtain ⟨hn, ht⟩ := body_cursor run
  simpa only [program, table, hn, ht] using
    PrimedCounter.Call.execute_body _ 29 30 pub st rs privateMem m run extra fuel

private theorem phase_run {pub : Pub → Word w} {st : Word w} {p : UniversalMachine.Program}
    {rs m es out mem} (run : Flow.Exec pub st (body (LiveEvaluatorRAMPrepare.prepare p)) rs m es out mem)
    (hs : st ≠ 0) :
    ∃ fs rc, Flow.Exec pub st cell (located (loaded pub st rs m) m) m fs rc mem ∧
      es = (List.replicate 11 .tick ++ [.read (pub 1) (m (pub 1).val)]) ++
        .tick :: ((locateEvents (loaded pub st rs m) m ++ fs) ++ List.replicate 8 .tick) := by
  cases run with
  | seq pre tail =>
    obtain ⟨rfl, rfl, rfl⟩ := unique_exec (by rfl) pre (load_exec ..)
    cases tail with
    | seq test close =>
      obtain ⟨rfl, rfl, rfl⟩ := unique_exec (by rfl) close (finish_exec ..)
      cases test with
      | ifEqYes ht _ => exact (hs ht).elim
      | ifEqNo _ data =>
        cases data with
        | seq loc checks =>
          obtain ⟨rfl, rfl, rfl⟩ := unique_exec (by rfl) loc (locate_exec ..)
          exact ⟨_, _, checks, by simp⟩

/-- Noninitial calls read the old state, three scratch words, one input
cell and one output cell. They never write or consume a choice. -/
theorem cell_call_cost {pub : Pub → Word w} {st : Word w} {p : UniversalMachine.Program} {rs m es out mem}
    (run : Flow.Exec pub st (body (LiveEvaluatorRAMPrepare.prepare p)) rs m es out mem) (hs : st ≠ 0) :
    mem = m ∧ choiceBits es = [] ∧ countProbes es = 6 := by
  obtain ⟨fs, rc, hr, rfl⟩ := phase_run run hs
  obtain ⟨rfl, hb, hc, _⟩ := cell_cost hr
  have probes (xs ys : List (Event w)) : countProbes (xs ++ ys) = countProbes xs + countProbes ys := by
    induction xs with
    | nil => simp [countProbes]
    | cons e xs ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]
  dsimp only [locateEvents]
  split_ifs <;> simp [probes, Flow.choiceBits_append, List.replicate_succ, choiceBits, countProbes, hb, hc]

/-- The initial call has exactly the preparation fragment's branch choices
and final scratch memory. Loading the public geometry and closing the
cursor are deterministic, including on an initially accepting evaluator. -/
theorem initial_choices_iff (p : UniversalMachine.Program) (pub : Pub → Word w)
    (rs : Regs w 32) (m mem : Memory w) (bs : List Bool) :
    (∃ es out, Flow.Exec pub 0 (body (LiveEvaluatorRAMPrepare.prepare p)) rs m es out mem ∧
      choiceBits es = bs) ↔
    ∃ es out, Flow.Exec pub 0 (LiveEvaluatorRAMPrepare.prepare p) (loaded pub 0 rs m) m es out mem ∧
      choiceBits es = bs := by
  constructor
  · rintro ⟨_, _, run, hb⟩
    cases run with
    | seq pre tail =>
      obtain ⟨rfl, rfl, rfl⟩ := unique_exec (by rfl) pre (load_exec ..)
      cases tail with
      | seq test close =>
        obtain ⟨rfl, rfl, rfl⟩ := unique_exec (by rfl) close (finish_exec ..)
        cases test with
        | ifEqNo ht _ => exact (ht rfl).elim
        | ifEqYes _ h =>
          exact ⟨_, _, h, by simpa [Flow.choiceBits_append, List.replicate_succ, choiceBits] using hb⟩
  · rintro ⟨es, out, h, hb⟩
    refine ⟨_, _, .seq (load_exec ..) (.seq (.ifEqYes rfl h) (finish_exec ..)), ?_⟩
    simp [Flow.choiceBits_append, List.replicate_succ, choiceBits, hb]

/-- The only choice list of a successful cell call is empty, its memory is
unchanged, and its local success predicate is exactly the cell comparison. -/
theorem noninitial_choices_iff (p : UniversalMachine.Program) (pub : Pub → Word w) {st : Word w}
    (hs : st ≠ 0) (rs : Regs w 32) (m mem : Memory w) (bs : List Bool) :
    (∃ es out, Flow.Exec pub st (body (LiveEvaluatorRAMPrepare.prepare p)) rs m es out mem ∧
      choiceBits es = bs) ↔
      cellTest (located (loaded pub st rs m) m) m ∧ bs = [] ∧ mem = m := by
  constructor
  · rintro ⟨es, out, run, hb⟩
    obtain ⟨hm, he, _⟩ := cell_call_cost run hs
    exact ⟨(noninitial_call_iff p pub hs rs m).mp ⟨_, _, _, run⟩, hb.symm.trans he, hm⟩
  · rintro ⟨hc, hb, hm⟩
    subst bs mem
    obtain ⟨es, out, mem, run⟩ := (noninitial_call_iff p pub hs rs m).mpr hc
    obtain ⟨rfl, hb, _⟩ := cell_call_cost run hs
    exact ⟨es, out, run, hb⟩

end LiveEvaluatorRAM.Schedule

end VPVNP
end Computability
end OAI
