import OAI.Computability.VPVNP.LiveEvaluatorSpace
import OAI.Computability.VPVNP.LiveModes

/-!
# Counting actual configuration strings on the live tail

For each of the `2^h` tail groups the input is either the initialized machine or
a decoded incoming cut. The output is either a decoded outgoing cut or the
mandatory accepting halt at the endpoint. Each interior cut checks the live
mode, the fixed-width word encoding of both tapes and the control, and zero
padding. The resulting count is the machine's accepting path count whenever
its accepting histories fit in the chosen tape window.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorTail

open UniversalMachine EvaluatorTail LiveEvaluatorEncoding CutSchedule

variable {h Δ M w : ℕ}

/-- The fixed fields and bit-capacity proofs shared by all groups of the tail. -/
structure Layout (extra M w Δ : ℕ) : Prop where
  symbolWidth : 2 ≤ w
  stateWidth : extra + 2 ≤ 2 ^ w
  cutWidth : 1 + fieldWords M * w ≤ Δ

variable {p : Program} (layout : Layout p.extra M w Δ)

private def fields (j : Fin (2 ^ h - 1)) :=
  tailLayout h Δ (2 ^ h + (j.val + 1)) (fieldWords M * w) (by omega)
    (by rw [pow_succ]; have := j.isLt; omega) layout.cutWidth

/-- The bits emitted at the cut after tail group `j + 1`. -/
def writeCut (j : Fin (2 ^ h - 1)) (s : Code p.extra M) :
    Bits (width (h + 1) Δ (2 ^ h + (j.val + 1))) :=
  (fields layout j).symm (true, (format layout.symbolWidth layout.stateWidth).encode s, fun _ => false)

/-- Parse all three fields, rejecting malformed words, mode, or padding. -/
def readCut (j : Fin (2 ^ h - 1)) (b : Bits (width (h + 1) Δ (2 ^ h + (j.val + 1)))) :
    Option (Code p.extra M) :=
  let f := fields layout j b
  if f.1 = true ∧ f.2.2 = fun _ => false then (format layout.symbolWidth layout.stateWidth).decode f.2.1
  else none

theorem readCut_iff (j : Fin (2 ^ h - 1)) (b : Bits (width (h + 1) Δ (2 ^ h + (j.val + 1))))
    (s : Code p.extra M) : readCut layout j b = some s ↔ b = writeCut layout j s := by
  constructor
  · unfold readCut
    dsimp only
    split
    · rename_i hv
      intro hd
      apply (fields layout j).injective
      rw [writeCut, Equiv.apply_symm_apply]
      exact Prod.ext hv.1 (Prod.ext ((decode_iff ..).mp hd) hv.2)
    · simp
  · rintro rfl
    simp [readCut, writeCut, decode_iff]

private def timeAfter (j : Fin (2 ^ h - 1)) : Fin (2 ^ h + 1) :=
  ⟨j.val + 1, by have := j.isLt; omega⟩

/-- The first tail group receives its initialized state from the middle
exponents. The last group compares its successor to the accepting halt. -/
def boundary (initialCode : Code p.extra M) (bits : LiveChain.TailBits h Δ)
    (i : Fin (2 ^ h + 1)) : Option (Code p.extra M) :=
  if h₀ : i.val = 0 then some initialCode else if hT : i.val = 2 ^ h then some .accepted
  else readCut layout ⟨i.val - 1, by omega⟩ (bits ⟨i.val - 1, by omega⟩)

@[simp] theorem boundary_zero (init : Code p.extra M) (bits : LiveChain.TailBits h Δ) :
    boundary layout init bits 0 = some init := by simp [boundary]

@[simp] theorem boundary_last (init : Code p.extra M) (bits : LiveChain.TailBits h Δ) :
    boundary layout init bits (Fin.last (2 ^ h)) = some .accepted := by simp [boundary]

private theorem boundary_after (init : Code p.extra M) (bits : LiveChain.TailBits h Δ)
    (j : Fin (2 ^ h - 1)) :
    boundary layout init bits (timeAfter j) = readCut layout j (bits j) := by
  simp [boundary, timeAfter, show j.val + 1 ≠ 2 ^ h by have := j.isLt; omega]

/-- Each physical group checks its two endpoints and one literal branch
choice. A rejecting halt fails the group that reaches it. -/
def Valid (init : Code p.extra M) (choice : Fin (2 ^ h) → Bool) (bits : LiveChain.TailBits h Δ) : Prop :=
  ∀ i, ∃ a b, boundary layout init bits i.castSucc = some a ∧
    boundary layout init bits i.succ = some b ∧ LiveEvaluatorStep.nextCode p a (choice i) = some b ∧
    b ≠ .rejected

private theorem successful_not_rejected (T : ℕ) (c : Config p.extra) (choice : Fin T → Bool)
    (ha : acceptsChoices p T c choice) (i : Fin (T + 1)) : history p T c choice i ≠ .rejected := by
  induction i using Fin.reverseInduction with
  | last => rw [(history_last ..).mpr ha]; simp
  | cast i ih =>
    intro hr
    apply ih
    rw [history_step, hr]
    rfl

/-- The accepted runs lie in the supplied tape-space bound at every group. -/
def HistoriesFit (p : Program) (M T : ℕ) (c : Config p.extra) : Prop :=
  ∀ choice, acceptsChoices p T c choice → ∀ i, StateFits M (history p T c choice i)

variable (c : Config p.extra) (init : Code p.extra M) (hi : init.toState = canonical c)
  (space : HistoriesFit p M (2 ^ h) c)

private def expectedCode (choice : Fin (2 ^ h) → Bool) (ha : acceptsChoices p (2 ^ h) c choice)
    (i : Fin (2 ^ h + 1)) : Code p.extra M :=
  Code.ofState (history p (2 ^ h) c choice i) (space choice ha i)

private theorem toState_expected (choice : Fin (2 ^ h) → Bool) (ha : acceptsChoices p (2 ^ h) c choice)
    (i : Fin (2 ^ h + 1)) :
    (expectedCode c space choice ha i).toState = history p (2 ^ h) c choice i :=
  congrArg Subtype.val ((codeEquiv p.extra M).apply_symm_apply
    ⟨history p (2 ^ h) c choice i, space choice ha i⟩)

private theorem toState_injective : Function.Injective (Code.toState (extra := p.extra) (M := M)) :=
  fun _ _ he => (codeEquiv p.extra M).injective (Subtype.ext he)

private def expectedBits (choice : Fin (2 ^ h) → Bool) (ha : acceptsChoices p (2 ^ h) c choice) :
    LiveChain.TailBits h Δ :=
  fun j => writeCut layout j (expectedCode c space choice ha (timeAfter j))

include hi in
private theorem boundary_expected (choice : Fin (2 ^ h) → Bool) (ha : acceptsChoices p (2 ^ h) c choice)
    (i : Fin (2 ^ h + 1)) :
    boundary layout init (expectedBits layout c space choice ha) i = some (expectedCode c space choice ha i) := by
  by_cases h₀ : i.val = 0
  · have he : i = 0 := Fin.ext h₀
    subst i
    rw [boundary_zero]
    exact congrArg some (toState_injective (by rw [hi, toState_expected, history_zero]))
  by_cases hT : i.val = 2 ^ h
  · have he : i = Fin.last (2 ^ h) := Fin.ext hT
    subst i
    rw [boundary_last]
    exact congrArg some (toState_injective (by rw [toState_expected, (history_last ..).mpr ha]; rfl))
  let j : Fin (2 ^ h - 1) := ⟨i.val - 1, by omega⟩
  have he : i = timeAfter j := Fin.ext (by dsimp [timeAfter, j]; omega)
  rw [he, boundary_after, readCut_iff]
  rfl

include hi in
private theorem valid_expected (choice : Fin (2 ^ h) → Bool) (ha : acceptsChoices p (2 ^ h) c choice) :
    Valid layout init choice (expectedBits layout c space choice ha) := by
  intro i
  refine ⟨_, _, boundary_expected layout c init hi space choice ha i.castSucc,
    boundary_expected layout c init hi space choice ha i.succ, ?_, ?_⟩
  · rw [LiveEvaluatorStep.nextCode_iff, toState_expected, toState_expected, history_step]
  · intro hr
    apply successful_not_rejected _ c choice ha i.succ
    rw [← toState_expected c space choice ha i.succ, hr]
    rfl

include hi in
private theorem boundary_history (choice : Fin (2 ^ h) → Bool) (bits : LiveChain.TailBits h Δ)
    (valid : Valid layout init choice bits) (i : Fin (2 ^ h + 1)) :
    ∃ s, boundary layout init bits i = some s ∧ s.toState = history p (2 ^ h) c choice i := by
  induction i using Fin.induction with
  | zero => exact ⟨init, boundary_zero .., hi.trans (history_zero ..).symm⟩
  | succ j ih =>
    obtain ⟨a, ha, hstate⟩ := ih
    obtain ⟨a', b, ha', hb, hn, _⟩ := valid j
    have he := Option.some.inj (ha.symm.trans ha')
    subst a'
    exact ⟨b, hb, ((LiveEvaluatorStep.nextCode_iff ..).mp hn).trans
      (by rw [hstate, history_step])⟩

include hi in
private theorem accepts_of_valid (choice : Fin (2 ^ h) → Bool) (bits : LiveChain.TailBits h Δ)
    (hv : Valid layout init choice bits) : acceptsChoices p (2 ^ h) c choice := by
  obtain ⟨s, hs, he⟩ := boundary_history layout c init hi choice bits hv (Fin.last (2 ^ h))
  rw [boundary_last, Option.some.injEq] at hs
  subst s
  exact (history_last ..).mp he.symm

/-- The only data counted are branch bits and the actual interior cut bits.
No configuration string is placed at either endpoint. -/
abbrev Runs (init : Code p.extra M) := (choice : Fin (2 ^ h) → Bool) ×
  {bits : LiveChain.TailBits h Δ // Valid layout init choice bits}

/-- On an accepting computation all cut fields are forced. Reading just the
bits at adjacent cuts conversely recovers a unique accepting computation. -/
def runsEquiv :
    {choice : Fin (2 ^ h) → Bool // acceptsChoices p (2 ^ h) c choice} ≃
    Runs (h := h) layout init where
  toFun choice := ⟨choice.val, expectedBits layout c space choice.val choice.property,
    valid_expected layout c init hi space choice.val choice.property⟩
  invFun run := ⟨run.1, accepts_of_valid layout c init hi run.1 run.2.val run.2.property⟩
  left_inv _ := rfl
  right_inv run := by
    rcases run with ⟨choice, bits, hv⟩
    refine Sigma.ext ?_ ?_
    · rfl
    apply heq_of_eq
    apply Subtype.ext
    funext j
    obtain ⟨s, hs, he⟩ := boundary_history layout c init hi choice bits hv (timeAfter j)
    rw [boundary_after, readCut_iff] at hs
    change writeCut layout j (expectedCode c space choice _ (timeAfter j)) = bits j
    rw [hs]
    exact congrArg (writeCut layout j) (toState_injective ((toState_expected ..).trans he.symm))

include hi space in
/-- The tail contributes exactly the clocked accepting path count, including
initial acceptance, early acceptance and coincident branching successors. -/
theorem card_runs : Nat.card (Runs (h := h) layout init) = paths p (2 ^ h) c := by
  rw [← Nat.card_congr (runsEquiv layout c init hi space), Nat.card_eq_fintype_card,
    Fintype.card_subtype, paths_eq_card_choices]

/-- Initialize the bounded fields from the tape machine at the middle cut. -/
def initialCode (M : ℕ) (c : Config p.extra) : Code p.extra M :=
  if ha : c.state.val = 1 then .accepted else if hz : c.state.val = 0 then .rejected else
    .running (ConfigWindow.ofConfig M c) (by change 2 ≤ c.state.val; omega)

theorem initialCode_toState (c : Config p.extra) (hf : StateFits M (canonical c)) :
    (initialCode M c).toState = canonical c := by
  by_cases ha : c.state.val = 1
  · simp [initialCode, canonical, ha, Code.toState]
  by_cases hz : c.state.val = 0
  · simp [initialCode, canonical, hz, Code.toState]
  simp only [canonical, ha, hz, ite_false] at hf
  simp [initialCode, canonical, ha, hz, Code.toState, hf.2]

open RAMTape RAMTape.StackCompiler

/-- For a bounded-head tape program all running states reached on a choice
string fit into a common window. This specializes the bit-string count with
no remaining hypothesis about the validity of individual configurations. -/
theorem card_of_head_bound (p : Program) (raw : UniversalMachine.Word) (R : ℕ)
    (bounded : ∀ bits, let d := choiceDisplacement p (initial p raw) bits; HeadBox R d.1 d.2)
    (layout : Layout p.extra (raw.length + R + R) w Δ) :
    Nat.card (Runs (h := h) layout (initialCode _ (initial p raw))) =
      paths p (2 ^ h) (initial p raw) := by
  apply card_runs
  · apply initialCode_toState
    exact LiveEvaluatorSpace.history_fits p raw R bounded 0 (fun i => i.elim0) 0
  · exact fun choice _ i => LiveEvaluatorSpace.history_fits p raw R bounded (2 ^ h) choice i

/-- Specialization to the literal two-tape machine emitted by the finite
stack compiler. The storage bound is required only on reachable stack states. -/
theorem card_labeled {K Q : Type*} [DecidableEq K] [Fintype K] [Fintype Q]
    (input : K) (code : StackCode K Q) (start : Q) (raw : UniversalMachine.Word) {B : ℕ}
    (bounded : ∀ ⦃q s⦄, Reach code start (labeledInput input raw) q s →
      Fintype.card K + 1 + ∑ a, (s a).length ≤ B)
    (layout : Layout (labeledProgram input code start).extra (raw.length + (7 * B + 4) + (7 * B + 4)) w Δ) :
    let E := labeledProgram input code start
    Nat.card (Runs (h := h) layout (initialCode _ (initial E raw))) = paths E (2 ^ h) (initial E raw) :=
  card_of_head_bound _ _ _ (input_space_labeled input code start raw bounded) layout

open ExponentTrace

/-- Recover the evaluator input from the counter words on the physical middle
cut, with the input format, advice and length parameter supplied by `assemble`. -/
def middleInput {t Z : ℕ} (hfit : 1 + t * Z ≤ Δ) (assemble : (Fin t → ℕ) → UniversalMachine.Word)
    (live : LiveBits h Δ) : UniversalMachine.Word :=
  assemble (fun a => (counters hfit live (Fin.last (2 ^ h)) a).val)

theorem middleInput_eq {t Z : ℕ} (hfit : 1 + t * Z ≤ Δ) (assemble : (Fin t → ℕ) → UniversalMachine.Word)
    (ξ : Exterior h Δ) (inc : Fin (2 ^ h) → Fin t → ℕ) (live : LiveBits h Δ)
    (valid : ExponentTrace.Valid hfit ξ inc live) :
    middleInput hfit assemble live = assemble (fun a => ∑ i, inc i a) :=
  congrArg assemble (funext (middle_counters hfit ξ inc live valid))

/-- The middle cut supplies the actual initial input to the first tail
transition. The count for the entire tail is the evaluator's accepting count
on the sum of the nominated production and gadget exponents. -/
theorem card_middle {t Z : ℕ} (hfit : 1 + t * Z ≤ Δ) (assemble : (Fin t → ℕ) → UniversalMachine.Word)
    (ξ : Exterior h Δ) (inc : Fin (2 ^ h) → Fin t → ℕ) (live : LiveBits h Δ)
    (valid : ExponentTrace.Valid hfit ξ inc live) (p : Program) (R : ℕ)
    (bounded : ∀ bits, let d := choiceDisplacement p (initial p (middleInput hfit assemble live)) bits
      HeadBox R d.1 d.2)
    (layout : Layout p.extra ((middleInput hfit assemble live).length + R + R) w Δ) :
    Nat.card (Runs (h := h) layout (initialCode _ (initial p (middleInput hfit assemble live)))) =
      paths p (2 ^ h) (initial p (assemble (fun a => ∑ i, inc i a))) := by
  rw [card_of_head_bound p _ R bounded, middleInput_eq hfit assemble ξ inc live valid]

end LiveEvaluatorTail

end VPVNP
end Computability
end OAI
