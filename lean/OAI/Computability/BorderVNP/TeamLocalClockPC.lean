import OAI.Computability.BorderVNP.TeamTapeHandoffLink
import OAI.Computability.VPVNP.RAMTapePublicExprArithmetic

/-!
# Restoring the program counter from a checked successor frame

A live receiver reverses the little-endian PC onto a scratch stack. As it
restores the bits, a finite table accumulates their value in most-significant
order. An out-of-range prefix stays out of range. An accepted halt requires
only the status bit and returns directly.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamLocalClockPC

open VPVNP RAMTape BurstRAM TeamTapeHandoff

variable {w p k : ℕ}

/-- The machine reads the status, PC and an empty scratch stack. -/
inductive Port where
  | tag | pc | tmp
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- A fixed instruction label, a propagated halt or a rejecting bad PC. -/
inductive Outcome (p : ℕ) where
  | live (pc : Fin p) | accepted | reject
  deriving DecidableEq, Fintype

/-- The PC accumulator is a fixed program label or the out-of-range marker. -/
inductive State (p : ℕ) where
  | status | restoreTag (b : Bool) | reverse | save (b : Bool)
  | read (acc : Option (Fin p)) | put (acc : Option (Fin p)) (b : Bool)
  | done (result : Outcome p)
  deriving DecidableEq, Fintype

private def clip (p n : ℕ) : Option (Fin p) :=
  if h : n < p then some ⟨n, h⟩ else none

private def extend (b : Bool) : Option (Fin p) → Option (Fin p)
  | some i => clip p (2 * i.val + b.toNat)
  | none => none

private theorem extend_clip (p n : ℕ) (b : Bool) :
    extend b (clip p n) = clip p (2 * n + b.toNat) := by
  by_cases h : n < p
  · simp [clip, h, extend]
  · have h' : ¬ 2 * n + b.toNat < p := by omega
    simp [clip, h, h', extend]

private def outcome : Option (Fin p) → Outcome p
  | none => .reject
  | some i => .live i

/-- Exact program-label dispatch on the unsigned value of a word. -/
def lookup (p n : ℕ) : Outcome p := outcome (clip p n)

theorem lookup_reject_iff (p n : ℕ) : lookup p n = .reject ↔ p ≤ n := by
  by_cases h : n < p
  · simp [lookup, clip, outcome, h, Nat.not_le.mpr h]
  · simp [lookup, clip, outcome, h, Nat.not_lt.mp h]

/-- This finite table depends on the instruction count and works for every width. -/
def code (p : ℕ) : StackCode Port (State p)
  | .status => .pop .tag (fun b => b.elim (.done .reject) .restoreTag)
  | .restoreTag b => .push .tag b (if b then .done .accepted else .reverse)
  | .reverse => .pop .pc (fun b => b.elim (.read (clip p 0)) .save)
  | .save b => .push .tmp b .reverse
  | .read a => .pop .tmp (fun b => b.elim (.done (outcome a)) (fun bit => .put (extend bit a) bit))
  | .put a b => .push .pc b (.read a)
  | .done .reject => .halt false
  | .done _ => .halt true

private def pcBank (tag pc tmp : List Bool) : Stacks Port
  | .tag => tag
  | .pc => pc
  | .tmp => tmp

private theorem update_stacks (tag pc tmp bits : List Bool) (port : Port) :
    Function.update (pcBank tag pc tmp) port bits = match port with
      | .tag => pcBank bits pc tmp
      | .pc => pcBank tag bits tmp
      | .tmp => pcBank tag pc bits := by
  funext j
  cases port <;> cases j <;> rfl

local macro "pc_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [pcBank, List.head?_nil, List.head?_cons, List.tail_cons, List.tail_nil,
    update_stacks, Option.elim_none, Option.elim_some])

private theorem reverse_run (p : ℕ) (tag pc tmp : List Bool) :
    StackRuns (code p) (2 * pc.length + 1) .reverse (pcBank tag pc tmp)
      (.read (clip p 0)) (pcBank tag [] (pc.reverse ++ tmp)) := by
  induction pc generalizing tmp with
  | nil =>
    simp only [List.length_nil, List.reverse_nil, List.nil_append, Nat.mul_zero, Nat.zero_add]
    pc_step
    exact .nil ..
  | cons b xs ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc]
    pc_step
    pc_step
    exact ih (b :: tmp)

private def digit (n : ℕ) (b : Bool) := 2 * n + b.toNat

private theorem fold_digits (xs : List Bool) :
    xs.reverse.foldl digit 0 = TapeWord.value xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp [List.reverse_cons, List.foldl_append, ih, digit, TapeWord.value, Nat.add_comm]

private theorem restore_run (p : ℕ) (tag pc tmp : List Bool) (acc : ℕ) :
    StackRuns (code p) (2 * tmp.length + 1) (.read (clip p acc)) (pcBank tag pc tmp)
      (.done (lookup p (tmp.foldl digit acc))) (pcBank tag (tmp.reverse ++ pc) []) := by
  induction tmp generalizing pc acc with
  | nil =>
    simp only [List.length_nil, List.reverse_nil, List.nil_append, Nat.mul_zero, Nat.zero_add]
    pc_step
    exact .nil ..
  | cons b xs ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.foldl_cons]
    pc_step
    pc_step
    rw [extend_clip]
    exact ih (b :: pc) (digit acc b)

private theorem status_run (p : ℕ) (b : Bool) (tag pc tmp : List Bool) :
    StackRuns (code p) 2 .status (pcBank (b :: tag) pc tmp)
      (if b then .done .accepted else .reverse) (pcBank (b :: tag) pc tmp) := by
  pc_step
  pc_step
  exact .nil ..

private theorem stack_eta (s : Stacks Port) : pcBank (s .tag) (s .pc) (s .tmp) = s := by
  funext i
  cases i <;> rfl

/-- On a live tag, decode any PC bit list and restore all three stacks exactly.
The same running time covers out-of-range PC values and an empty program. -/
theorem live_run (p : ℕ) (s : Stacks Port) (tail : List Bool)
    (tag : s .tag = false :: tail) (scratch : s .tmp = []) :
    StackRuns (code p) (4 * (s .pc).length + 4) .status s
      (.done (lookup p (TapeWord.value (s .pc)))) s := by
  have start := status_run p false tail (s .pc) []
  have scan := reverse_run p (false :: tail) (s .pc) []
  have restore := restore_run p (false :: tail) [] (s .pc).reverse 0
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil, fold_digits] at restore
  rw [List.append_nil] at scan
  have he : pcBank (false :: tail) (s .pc) [] = s := by rw [← tag, ← scratch, stack_eta]
  rw [he] at start scan restore
  rw [show 4 * (s .pc).length + 4 =
    (2 + (2 * (s .pc).length + 1)) + (2 * (s .pc).length + 1) by omega]
  exact (start.trans scan).trans restore

/-- Halt propagation preserves the decoded frame without looking up an instruction. -/
theorem halted_run (p : ℕ) (s : Stacks Port) (tail : List Bool) (tag : s .tag = true :: tail) :
    StackRuns (code p) 2 .status s (.done .accepted) s := by
  simpa only [← tag, stack_eta, ite_true] using status_run p true tail (s .pc) (s .tmp)

/-- The names of the three physical stacks in the receiver's decoded bank. -/
def framePorts : Port → Codec.Port k
  | .tag => .tag
  | .pc => .field 0
  | .tmp => .tmp

theorem framePorts_injective : Function.Injective (@framePorts k) := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

/-- The actual live PC occupies field zero of the decoded bank. -/
theorem frame_pc (pc ticks : Word w) (regs : Fin k → Word w) (suffix : List Bool) :
    Codec.bank (.live pc regs ticks) suffix (framePorts .pc) = wordBits pc := rfl

/-- On an incoming live frame, the exact program label is recovered if it fits the program.
The caller can redirect the terminal labels, and its full bank is preserved. -/
theorem frame_live_run {Q : Type} (p : ℕ) (pc ticks : Word w) (regs : Fin k → Word w)
    (suffix : List Bool) (labels : State p → Q) (target : StackCode (Codec.Port k) Q)
    (rows : ∀ q, ((code p) q).returns = false →
      target (labels q) = ((code p) q).rename framePorts labels) :
    let s := Codec.bank (.live pc regs ticks) suffix
    StackRuns target (4 * w + 4) (labels .status) s (labels (.done (lookup p pc.val))) s := by
  let s := Codec.bank (.live pc regs ticks) suffix
  have base := live_run p (s ∘ framePorts) [] rfl rfl
  have h := base.lift framePorts framePorts_injective labels s rows
  have he := installStacks_eq framePorts_injective s (s ∘ framePorts) (fun _ => rfl)
  simpa only [he, Function.comp_apply, s, frame_pc, length_wordBits,
    TapeWord.value_wordBits] using h

/-- A PC packed from any actual label is recovered exactly when the program fits the width. -/
theorem lookup_packed (pc : Fin p) (fits : p ≤ 2 ^ w) :
    lookup p (PublicExprMachine.packed w pc.val).val = .live pc := by
  rw [PublicExprMachine.packed_val (pc.isLt.trans_le fits)]
  simp [lookup, outcome, clip, pc.isLt]

/-- The accepted frame takes the short halt branch on any caller continuation. -/
theorem frame_halted_run {Q : Type} (p : ℕ) (ticks : Word w) (suffix : List Bool)
    (labels : State p → Q) (target : StackCode (Codec.Port k) Q)
    (rows : ∀ q, ((code p) q).returns = false →
      target (labels q) = ((code p) q).rename framePorts labels) :
    let s := Codec.bank (.accepted ticks) suffix
    StackRuns target 2 (labels .status) s (labels (.done .accepted)) s := by
  let s : Stacks (Codec.Port k) := Codec.bank (.accepted ticks) suffix
  have h := (halted_run p (s ∘ framePorts) [] rfl).lift
    framePorts framePorts_injective labels s rows
  simpa only [installStacks_eq framePorts_injective s (s ∘ framePorts) (fun _ => rfl)] using h

end TeamLocalClockPC

end BorderVNP
end Computability
end OAI
