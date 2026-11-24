import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete
import OAI.Computability.VPVNP.RAMRecords

/-!
# Checking one tape cell of a live evaluator transition

Each scheduled cell call reads one old symbol and one proposed new symbol.
The head-relative window is shifted cyclically at its endpoints. At a clipped
endpoint, the overwritten old symbol must be blank and the newly exposed
cell is checked against that blank. Thus every input and every output cell
is examined, including when the radius is zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAM

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM

/-- The register indices of the 32-register native evaluator transition checker. -/
abbrev Reg := Fin 32
/-- Native transition-checking code over 32 registers and a parameterized public operand bank. -/
abbrev Code (k : ℕ) := Flow 32 k

variable {w k : ℕ}

/-- Can this fragment reach its normal exit with the stated postcondition? -/
def exits (pub : Fin k → Word w) (state : Word w) (a : Code k)
    (rs : Regs w 32) (m : Memory w) (post : Regs w 32 → Memory w → Prop) :=
  ∃ es out mem, Flow.Exec pub state a rs m es out mem ∧ post out mem

theorem exits_seq (pub : Fin k → Word w) (state : Word w) (a b : Code k)
    (rs : Regs w 32) (m : Memory w) (post : Regs w 32 → Memory w → Prop) :
    exits pub state (.seq a b) rs m post ↔
      exits pub state a rs m (fun r u => exits pub state b r u post) := by
  constructor
  · rintro ⟨_, _, _, h, hp⟩
    cases h with
    | seq ha hb => exact ⟨_, _, _, ha, _, _, _, hb, hp⟩
  · rintro ⟨_, _, _, ha, _, _, _, hb, hp⟩
    exact ⟨_, _, _, .seq ha hb, hp⟩

theorem exits_line (pub : Fin k → Word w) (state : Word w) (op : Op 32 k)
    (rs : Regs w 32) (m : Memory w) (post : Regs w 32 → Memory w → Prop) :
    exits pub state (.line op) rs m post ↔
      ∃ e out mem, op.effect pub state rs m = some (e, out, mem) ∧ post out mem := by
  constructor
  · rintro ⟨_, _, _, h, hp⟩
    cases h with | line he => exact ⟨_, _, _, he, hp⟩
  · rintro ⟨_, _, _, h, hp⟩
    exact ⟨_, _, _, .line h, hp⟩

theorem exits_ifEq (pub : Fin k → Word w) (state : Word w) (i j : Reg) (a b : Code k)
    (rs : Regs w 32) (m : Memory w) (post : Regs w 32 → Memory w → Prop) :
    exits pub state (.ifEq i j a b) rs m post ↔
      if rs i = rs j then exits pub state a rs m post else exits pub state b rs m post := by
  constructor
  · rintro ⟨_, _, _, h, hp⟩
    cases h with
    | ifEqYes ht hb => exact (ite_eq_left ht).symm ▸ ⟨_, _, _, hb, hp⟩
    | ifEqNo ht hb => exact (ite_eq_right ht).symm ▸ ⟨_, _, _, hb, hp⟩
  · split
    · rename_i h
      rintro ⟨_, _, _, ha, hp⟩
      exact ⟨_, _, _, .ifEqYes h ha, hp⟩
    · rename_i h
      rintro ⟨_, _, _, hb, hp⟩
      exact ⟨_, _, _, .ifEqNo h hb, hp⟩

private def line (op : Op 32 k) : Code k := .line op

private def add (dst x y : Reg) : Code k := line (.binary .add dst x y)

private def guardEq (x y : Reg) : Code k := line (.guardEq x y)

private def fetch (dst base idx : Reg) : Code k :=
  .seq (add 20 base idx) (line (.read dst 20))

/-- Compare the symbol at an output index to a specified register. -/
private def compareCell (idx expect : Reg) : Code k :=
  .seq (fetch 21 15 idx) (guardEq 21 expect)

/-- For a running target the old cell either maps to an adjacent output cell,
or leaves the window and pairs with the newly exposed blank. -/
private def moved (expect : Reg) : Code k :=
  .ifEq 7 0 (compareCell 13 expect)
    (.ifEq 7 1
      (.ifEq 13 12 (.seq (guardEq expect 0) (compareCell 0 expect))
        (.seq (add 19 13 1) (compareCell 19 expect)))
      (.ifEq 13 0 (.seq (guardEq expect 0) (compareCell 12 expect))
        (.seq (line (.binary .sub 19 13 1)) (compareCell 19 expect))))

/-- Registers 0–3 contain their literal values, 5 is the target state, 6 and
7 are this tape's write symbol and move, 11 and 12 are the radius and last
cell, 13 is the old cell index, 14 and 15 are the old and new tape-field base
addresses, and 16 is the source state. Scratch registers are 17 and 19–21. -/
def cell : Code k :=
  .seq (fetch 17 14 13) (.seq
    (.ifEq 16 1 (guardEq 17 0) (line (.guardLt 17 3)))
    (.ifEq 5 1 (compareCell 13 0)
      (.ifEq 13 11 (moved 6) (moved 17))))

private theorem exits_add (pub : Fin k → Word w) (state : Word w) (dst x y : Reg)
    (rs : Regs w 32) (m : Memory w) (post : Regs w 32 → Memory w → Prop) :
    exits pub state (add dst x y) rs m post ↔ post (Function.update rs dst (rs x + rs y)) m := by
  simp [add, line, exits_line, Op.effect, BinaryOp.eval]

private theorem exits_guardEq (pub : Fin k → Word w) (state : Word w) (x y : Reg)
    (rs : Regs w 32) (m : Memory w) (post : Regs w 32 → Memory w → Prop) :
    exits pub state (guardEq x y) rs m post ↔ rs x = rs y ∧ post rs m := by
  simp [guardEq, line, exits_line, Op.effect]

private theorem exits_fetch (pub : Fin k → Word w) (state : Word w) (dst base idx : Reg)
    (rs : Regs w 32) (m : Memory w) (post : Regs w 32 → Memory w → Prop) :
    exits pub state (fetch dst base idx) rs m post ↔
      post (Function.update (Function.update rs 20 (rs base + rs idx)) dst
        (m (rs base + rs idx).val)) m := by
  simp [fetch, exits_seq, exits_add, line, exits_line, Op.effect]

private theorem exits_compare (pub : Fin k → Word w) (state : Word w) (idx expect : Reg)
    (he : expect ≠ 20) (hf : expect ≠ 21) (rs : Regs w 32) (m : Memory w) :
    exits pub state (compareCell idx expect) rs m (fun _ _ => True) ↔
      m (rs 15 + rs idx).val = rs expect := by
  simp [compareCell, exits_seq, exits_fetch, exits_guardEq, Function.update_of_ne, he, hf]

/-- Destination of an old cell in head-relative word coordinates, with the
clipped endpoint paired to the newly exposed opposite endpoint. -/
def destination (zero one last move i : Word w) : Word w :=
  if move = zero then i
  else if move = one then (if i = last then zero else i + one)
  else if i = zero then last else i - one

/-- Whether the written old symbol would move outside the window. -/
def clipped (zero one last move i : Word w) : Prop :=
  move ≠ zero ∧ (if move = one then i = last else i = zero)

private theorem exits_moved (pub : Fin k → Word w) (state : Word w) (expect : Reg)
    (he : expect ≠ 19) (hf : expect ≠ 20) (hg : expect ≠ 21) (rs : Regs w 32) (m : Memory w) :
    exits pub state (moved expect) rs m (fun _ _ => True) ↔
      (clipped (rs 0) (rs 1) (rs 12) (rs 7) (rs 13) → rs expect = rs 0) ∧
      m (rs 15 + destination (rs 0) (rs 1) (rs 12) (rs 7) (rs 13)).val = rs expect := by
  simp only [moved, exits_ifEq, exits_seq, exits_add, exits_guardEq, exits_compare _ _ _ _ hf hg,
    destination, clipped]
  split_ifs <;> simp_all (config := { decide := true }) [line, exits_line, Op.effect, BinaryOp.eval,
    Function.update_of_ne]

/-- Local condition on the two addressed memory words. The first condition
validates the source symbol, even if the transition overwrites it. A halting
target has zero in every cell. -/
def cellTest (rs : Regs w 32) (m : Memory w) : Prop :=
  let old := m (rs 14 + rs 13).val
  (if rs 16 = rs 1 then old = rs 0 else old < rs 3) ∧
    if rs 5 = rs 1 then m (rs 15 + rs 13).val = rs 0 else
      let written := if rs 13 = rs 11 then rs 6 else old
      (clipped (rs 0) (rs 1) (rs 12) (rs 7) (rs 13) → written = rs 0) ∧
      m (rs 15 + destination (rs 0) (rs 1) (rs 12) (rs 7) (rs 13)).val = written

/-- Successful execution of the fixed cell code is equivalent to checking
the source, the clipped boundary and the proposed output symbol. -/
theorem cell_exec_iff (pub : Fin k → Word w) (state : Word w) (rs : Regs w 32) (m : Memory w) :
    (∃ es out mem, Flow.Exec pub state cell rs m es out mem) ↔ cellTest rs m := by
  have h : (∃ es out mem, Flow.Exec pub state cell rs m es out mem) ↔
      exits pub state cell rs m (fun _ _ => True) := by simp [exits]
  rw [h]
  simp (config := { decide := true }) only [cell, exits_seq, exits_fetch, exits_ifEq, exits_guardEq,
    exits_compare, exits_moved, cellTest, Function.update_self]
  split_ifs <;> simp_all (config := { decide := true }) [line, exits_line, Op.effect]

/-- Certify a fixed read count for acyclic code with neither writes nor
choices. Both continuations of a comparison must have the same read count. -/
private def reads : Code k → Option ℕ
  | .line (.read ..) => some 1
  | .line (.write ..) => none
  | .line _ => some 0
  | .seq a b => Option.map₂ (· + ·) (reads a) (reads b)
  | .ifEq _ _ a b | .ifLt _ _ a b => if reads a = reads b then reads a else none
  | .branch .. | .whileLt .. => none

private theorem probes_append (a b : List (Event w)) :
    countProbes (a ++ b) = countProbes a + countProbes b := by
  induction a with
  | nil => simp [countProbes]
  | cons e a ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

private theorem reads_line {pub : Fin k → Word w} {st : Word w} {rs : Regs w 32} {m : Memory w}
    {op : Op 32 k} {e out mem n} (h : op.effect pub st rs m = some (e, out, mem))
    (hr : reads (.line op) = some n) :
    mem = m ∧ choiceBits [e] = [] ∧ countProbes [e] = n := by
  cases op <;> simp_all [Op.effect, reads]
  all_goals subst n
  all_goals rcases h with ⟨_, rfl, rfl, rfl⟩
  all_goals try subst e
  all_goals constructor <;> rfl

private theorem reads_sound {pub : Fin k → Word w} {st : Word w} {a : Code k} {rs m es out mem}
    (run : Flow.Exec pub st a rs m es out mem) {n} (h : reads a = some n) :
    mem = m ∧ choiceBits es = [] ∧ countProbes es = n ∧ es.length ≤ a.length := by
  induction run generalizing n with
  | line he =>
    obtain ⟨hm, hb, hc⟩ := reads_line he h
    exact ⟨hm, hb, hc, le_rfl⟩
  | seq _ _ ih₁ ih₂ =>
    simp only [reads, Option.map₂_eq_some_iff] at h
    obtain ⟨i, j, hi, hj, rfl⟩ := h
    obtain ⟨rfl, hb, hc, hl⟩ := ih₁ hi
    obtain ⟨rfl, hb', hc', hl'⟩ := ih₂ hj
    simp [Flow.choiceBits_append, probes_append, hb, hb', hc, hc', Flow.length, Nat.add_le_add hl hl']
  | ifEqYes _ _ ih | ifLtYes _ _ ih | ifEqNo _ _ ih | ifLtNo _ _ ih =>
    simp only [reads] at h
    split at h
    next eq =>
      obtain ⟨rfl, hb, hc, hl⟩ := ih (by first | exact h | exact eq ▸ h)
      simp [choiceBits, countProbes, hb, hc, Flow.length]; omega
    next => contradiction
  | branchYes | branchNo | whileDone | whileStep => contradiction

/-- Each successful cell check makes exactly two read probes, consumes no
choice bit and leaves the external memory unchanged. -/
theorem cell_cost {pub : Fin k → Word w} {st : Word w} {rs m es out mem}
    (run : Flow.Exec pub st cell rs m es out mem) :
    mem = m ∧ choiceBits es = [] ∧ countProbes es = 2 ∧ es.length ≤ (cell : Code k).length :=
  reads_sound run rfl

/-- Loop-free fragments have a fixed maximum instruction count across
all branch choices, independent of word width and tape radius. -/
def loopFree {r k : ℕ} : Flow r k → Bool
  | .line _ => true
  | .seq a b | .ifEq _ _ a b | .ifLt _ _ a b | .branch a b => loopFree a && loopFree b
  | .whileLt .. => false

theorem length_le_of_loopFree {r k : ℕ} {a : Flow r k} {pub : Fin k → Word w} {st : Word w}
    {rs m es out mem} (run : Flow.Exec pub st a rs m es out mem) (h : loopFree a = true) :
    es.length ≤ a.length := by
  induction run with
  | line => exact le_rfl
  | seq _ _ ih₁ ih₂ =>
    simp only [loopFree, Bool.and_eq_true] at h
    simpa only [List.length_append, Flow.length] using Nat.add_le_add (ih₁ h.1) (ih₂ h.2)
  | ifEqYes _ _ ih | ifLtYes _ _ ih | branchYes _ ih =>
    simp only [loopFree, Bool.and_eq_true] at h
    have hl := ih h.1
    simp only [List.length_cons, Flow.length]; omega
  | ifEqNo _ _ ih | ifLtNo _ _ ih | branchNo _ ih =>
    simp only [loopFree, Bool.and_eq_true] at h
    have hl := ih h.2
    simp only [List.length_cons, Flow.length]; omega
  | whileDone | whileStep => contradiction

theorem cell_loopFree : loopFree (cell : Code k) = true := rfl

end LiveEvaluatorRAM

end VPVNP
end Computability
end OAI
