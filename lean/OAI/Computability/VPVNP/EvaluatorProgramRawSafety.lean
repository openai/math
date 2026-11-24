import OAI.Computability.VPVNP.EvaluatorProgramMonomial
import OAI.Computability.VPVNP.EvaluatorMonomialSafety

/-!
# All-branch resources from the raw input to the monomial result

The parser and native converter have polynomial deterministic clocks. The
digit traversal may run for exponentially many steps while respecting its
polynomial stack bound. Each framed callback retains its safety certificate
on both successors of every binary choice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorRoutineSafety

open RAMTape

variable {K L : Type} [DecidableEq K] [DecidableEq L]

private theorem safeFrom_framed (r : FiniteRoutine K) (p : K → L)
    (frame : Stacks K → Stacks L) (read : ∀ s k, frame s (p k) = s k)
    (write : ∀ s k bits, Function.update (frame s) (p k) bits = frame (Function.update s k bits))
    (small : Stacks K → Prop) (large : Stacks L → Prop) (hs : ∀ s, small s → large (frame s))
    (cont : ℕ → Stacks L → Prop) (n : ℕ) (q : Option r.State) (s : Stacks K)
    (h : r.body.SafeFrom small (fun left u => cont left (frame u)) n q s) :
    (r.onPorts p).body.SafeFrom large cont n q (frame s) := by
  induction n generalizing q s with
  | zero => cases q <;> exact h
  | succ n ih =>
    cases q with
    | none => exact h
    | some q =>
      simp only [Routine.SafeFrom] at h ⊢
      refine ⟨hs s h.1, ?_⟩
      have hcode : (r.onPorts p).body.code q = (r.body.code q).rename p id := rfl
      rw [hcode]
      have hh := h.2
      cases he : r.body.code q <;> rw [he] at hh <;>
        simp only [StackOp.rename, id_eq, Function.comp_apply, read, write] at *
      all_goals first | exact ih _ _ hh | exact ⟨ih _ _ hh.1, ih _ _ hh.2⟩

/-- Preserve the stopping and peak-space contract under an embedding of
stack banks which commutes with every physical read and write. -/
theorem Bounded.onPorts_frame {S T : Type*} (r : FiniteRoutine K) (p : K → L)
    (frame : Stacks K → Stacks L) (read : ∀ s k, frame s (p k) = s k)
    (write : ∀ s k bits, Function.update (frame s) (p k) bits = frame (Function.update s k bits))
    {small : Stacks K → Prop} {large : Stacks L → Prop} (hs : ∀ s, small s → large (frame s))
    {pre : S → Stacks K} {post : T → Stacks K} {B : ℕ} (h : Bounded r.body small pre post B) :
    Bounded (r.onPorts p).body large (frame ∘ pre) (frame ∘ post) B := by
  intro extra fuel hf x cont hc
  exact safeFrom_framed r p frame read write small large hs cont fuel (some r.body.entry) (pre x)
    (h extra fuel hf x _ hc)

end EvaluatorRoutineSafety

namespace EvaluatorProgramMonomial

open RAMTape EvaluatorRoutineSafety EvaluatorDigitFetch EvaluatorMonomialSchedule
  EvaluatorChronologicalLoop EvaluatorRadixRows EvaluatorProgramRawInput

variable {P S : Type} [DecidableEq P] {t Z : ℕ}

/-- Input sizes and converter clock are polynomial in the exponent width,
label count, divisor bit width and callback storage. -/
def nativeSpace (t Z ℓ space : ℕ) :=
  (t*Z+t+Z+ℓ+space) + EvaluatorProgramInput.convertTicks t Z ℓ + schedulerSpace (t*(Z*ℓ)) t Z ℓ space

/-- Upper bound on the encoded input length from the advice size, number of labels and binary
exponent width. -/
def inputLengthBound (t Z A : ℕ) := A + (2*(t*Z)+6*Z+4)

/-- Time allowance for parsing the tagged raw input, bounded by twice its length bound plus one
instruction. -/
def readerBudget (t Z A : ℕ) := 2*inputLengthBound t Z A + 1

/-- Stack-space bound covering the raw input, parser workspace and the subsequent converted
monomial execution. -/
def rawSpace (t Z ℓ space A : ℕ) :=
  inputLengthBound t Z A + readerBudget t Z A + nativeSpace t Z ℓ space

/-- The closed physical storage bound is a degree-four polynomial in the
label count, exponent width, divisor width, callback space, and advice size. -/
theorem rawSpace_le_power (t Z ℓ space A : ℕ) :
    rawSpace t Z ℓ space A ≤ 150*(t+Z+ℓ+space+A+1)^4 := by
  let M := t+Z+ℓ+space+A+1
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hmono : rawSpace t Z ℓ space A ≤ rawSpace M M M M M := by
    unfold rawSpace nativeSpace readerBudget inputLengthBound EvaluatorProgramInput.convertTicks
      rowsTicks rowTicks EvaluatorRadixDivision.radixTicks EvaluatorRadixDivision.digitTicks
      schedulerSpace bankSpace
    gcongr <;> dsimp [M] <;> omega
  have expand : rawSpace M M M M M = 10*M^4 + 33*M^3 + 45*M^2 + 40*M + 21 := by
    unfold rawSpace nativeSpace readerBudget inputLengthBound EvaluatorProgramInput.convertTicks
      rowsTicks rowTicks EvaluatorRadixDivision.radixTicks EvaluatorRadixDivision.digitTicks
      schedulerSpace bankSpace
    ring
  have h₀ := Nat.pow_pos hM (n := 4)
  have h₁ : M ≤ M^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hM (by decide : 1 ≤ 4)
  have h₂ := Nat.pow_le_pow_right hM (by decide : 2 ≤ 4)
  have h₃ := Nat.pow_le_pow_right hM (by decide : 3 ≤ 4)
  change _ ≤ 150*M^4
  rw [expand] at hmono
  omega

variable (e : Fin t → BurstRAM.Word Z) (d : List Bool) (payload : S → Stacks P)
    (space : ℕ) (hp : ∀ x p, (payload x p).length ≤ space)
    (frobenius multiply : FiniteRoutine (Port P)) (BF BM : ℕ)

local notation "data" => packedTable d.length (TapeWord.value d) (List.ofFn e)
local notation "sFits" => stackFits (schedulerSpace (List.length data) t Z d.length space)
local notation "post" => fun x => EvaluatorProgramInput.extend Z d (bank data t Z d.length 0 0 0 0 (payload x))
local notation "ticks" => EvaluatorProgramInput.convertTicks t Z d.length + budget t Z d.length (TapeWord.value d) BF BM

omit [DecidableEq P] in
theorem extend_fits (s : Stacks (Port P)) (hs : sFits s) :
    stackFits (nativeSpace t Z d.length space) (EvaluatorProgramInput.extend Z d s) := by
  intro k
  cases k with
  | sched k =>
    have h := hs k
    simp only [packedTable_length, List.length_ofFn] at h
    exact h.trans (Nat.le_add_left ..)
  | word k => cases k <;> simp [EvaluatorProgramInput.extend, nativeSpace]; omega
  | _ => simp [EvaluatorProgramInput.extend, nativeSpace] <;> omega

private theorem extend_update (s : Stacks (Port P)) (k : Port P) (bits : List Bool) :
    Function.update (EvaluatorProgramInput.extend Z d s) (.sched k) bits =
      EvaluatorProgramInput.extend Z d (Function.update s k bits) := by
  funext j
  cases j with
  | sched a => by_cases ha : a = k <;> simp [EvaluatorProgramInput.extend, ha]
  | word a => cases a <;> rfl
  | _ => rfl

include hp in
omit [DecidableEq P] in
private theorem initial_length (x : S) (k : EvaluatorProgramInput.Port P) :
    (EvaluatorProgramInput.initial e d (payload x) k).length ≤ t*Z+t+Z+d.length+space := by
  cases k with
  | sched k =>
    have h := bank_length [] t Z d.length space payload hp (i := 0) (left := 0) (by omega)
      (j := 0) (cols := Z) (by omega) x k
    simp only [bankSpace, List.length_nil] at h
    exact h.trans (by omega)
  | word k => cases k <;> simp [EvaluatorProgramInput.initial, EvaluatorProgramInput.extend] <;> omega
  | _ => simp [EvaluatorProgramInput.initial, EvaluatorProgramInput.extend] <;> omega

include hp in
/-- All paths of the native converter and the physical scheduler satisfy
the resource bound, including paths that reject inside a callback. -/
theorem native_bounded (hq : 2 ≤ TapeWord.value d)
    (hf : ∀ (j : Fin Z) left, j.val + left < Z → Bounded frobenius.body sFits
      (fun x => bank data t Z d.length 0 j 0 left (payload x))
      (fun x => bank data t Z d.length 0 j 0 left (payload x)) BF)
    (hm : ∀ (i : Fin t) (j : Fin Z) labels cols, i.val + labels < t → j.val + cols < Z →
      ∀ bits : List Bool, bits.length = d.length →
      let pre (x : S) := EvaluatorDigitRepeat.frame Port.digit Port.borrow
        (bank data t Z d.length i j labels cols (payload x)) bits []
      Bounded multiply.body sFits pre pre BM) :
    Bounded (nativeMachine frobenius multiply).body (stackFits (nativeSpace t Z d.length space))
      (EvaluatorProgramInput.initial e d ∘ payload) post ticks := by
  let pre (x : S) := bank data t Z d.length 0 0 0 Z (payload x)
  have h₁ : Bounded EvaluatorProgramInput.convert.body (stackFits (nativeSpace t Z d.length space))
      (EvaluatorProgramInput.initial e d ∘ payload) (EvaluatorProgramInput.extend Z d ∘ pre)
      (EvaluatorProgramInput.convertTicks t Z d.length) := by
    apply Bounded.of_runs_with_room (g := id)
    · intro x
      exact ⟨_, le_rfl, EvaluatorProgramInput.convert_runs e d (payload x) hq⟩
    · intro x u hu k
      have h := initial_length e d payload space hp x k
      have hh := hu k
      simp only [Function.comp_apply] at hh
      unfold nativeSpace
      omega
  have hs := machine_bounded e d.length (TapeWord.value d) BF BM space payload hp
    frobenius multiply (by omega) (TapeWord.value_lt d).le hf hm
  have h₂ := Bounded.onPorts_frame (machine frobenius multiply) EvaluatorProgramInput.Port.sched
    (EvaluatorProgramInput.extend Z d) (fun _ _ => rfl) (extend_update d) (extend_fits e d space) hs
  exact h₁.followedBy h₂

private theorem frame_update (s : Stacks (EvaluatorProgramInput.Port P)) (k : EvaluatorProgramInput.Port P)
    (bits : List Bool) :
    Function.update (Evaluator.InputBank.frame [] s) (some k) bits =
      Evaluator.InputBank.frame [] (Function.update s k bits) := by
  funext j
  cases j with
  | none => rfl
  | some a => by_cases ha : a = k <;> simp [Evaluator.InputBank.frame, ha]

/-- Load the raw stream with its deterministic polynomial-space parser, then
preserve the resource certificate of the entire native machine. -/
theorem raw_bounded_of_native (ps : List P) (hn : ps.Nodup) (hall : ∀ p, p ∈ ps) (A : ℕ)
    (ha : ∀ x, (advice ps t d (payload x)).length ≤ A)
    (h : Bounded (nativeMachine frobenius multiply).body (stackFits (nativeSpace t Z d.length space))
      (EvaluatorProgramInput.initial e d ∘ payload) post ticks) :
    Bounded (rawMachine ps frobenius multiply).body (stackFits (rawSpace t Z d.length space A))
      (fun x => Evaluator.InputBank.frame (advice ps t d (payload x) ++ runtime e) (fun _ => []))
      (Evaluator.InputBank.frame [] ∘ (post)) (readerBudget t Z A + (ticks)) := by
  have h₁ : Bounded (Evaluator.InputBank.reader (fields ps)).body (stackFits (rawSpace t Z d.length space A))
      (fun x => Evaluator.InputBank.frame (advice ps t d (payload x) ++ runtime e) (fun _ => []))
      (fun x => Evaluator.InputBank.frame [] (EvaluatorProgramInput.initial e d (payload x)))
      (readerBudget t Z A) := by
    apply Bounded.of_runs_with_room (g := id)
    · intro x
      refine ⟨_, ?_, reader_runs ps hn hall e d (payload x)⟩
      have hr := readTicks_le ps e d (payload x)
      rw [runtime_length] at hr
      have hax := ha x
      unfold readerBudget inputLengthBound
      omega
    · intro x u hu k
      have hlen : (advice ps t d (payload x) ++ runtime e).length ≤ inputLengthBound t Z A := by
        simp only [inputLengthBound, List.length_append, runtime_length]
        exact Nat.add_le_add_right (ha x) _
      have hh := hu k
      cases k <;> simp only [Evaluator.InputBank.frame, List.length_nil] at hh
      all_goals unfold rawSpace; omega
  apply h₁.followedBy
  apply Bounded.onPorts_frame (nativeMachine frobenius multiply) some (Evaluator.InputBank.frame [])
    (fun _ _ => rfl) frame_update _ h
  intro s hs k
  cases k with
  | none => exact Nat.zero_le _
  | some k => exact (hs k).trans (Nat.le_add_left ..)

include hp in
/-- A physical stopping clock and a polynomial bound on every reachable
stack in the machine starting on the sole raw input tape. -/
theorem raw_space_clock (ps : List P) (hn : ps.Nodup) (hall : ∀ p, p ∈ ps) (A : ℕ)
    (ha : ∀ x, (advice ps t d (payload x)).length ≤ A)
    (h : Bounded (nativeMachine frobenius multiply).body (stackFits (nativeSpace t Z d.length space))
      (EvaluatorProgramInput.initial e d ∘ payload) post ticks) (outcome : Bool) (x : S) :
    let r := (rawMachine ps frobenius multiply).body
    let start := Evaluator.InputBank.frame (advice ps t d (payload x) ++ runtime e) (fun _ => [])
    StopsWithin (r.close outcome) (1+(readerBudget t Z A + (ticks))) (some r.entry) start ∧
      ∀ ⦃q s⦄, StackCompiler.Reach (r.close outcome) (some r.entry) start q s →
        stackFits (rawSpace t Z d.length space A) s := by
  have hh := raw_bounded_of_native e d payload space frobenius multiply BF BM ps hn hall A ha h
  have hpost (y : S) : stackFits (nativeSpace t Z d.length space) ((post) y) := by
    apply extend_fits e d space
    intro k
    have hs := bank_length data t Z d.length space payload hp (i := 0) (left := 0) (by omega)
      (j := 0) (cols := 0) (by omega) y k
    exact hs.trans (by unfold schedulerSpace; omega)
  have endSafe := hh 1 _ le_rfl x (fun n s => 0 < n ∧ stackFits (rawSpace t Z d.length space A) s) (by
    intro y n hn
    refine ⟨hn, fun k => ?_⟩
    cases k with
    | none => exact Nat.zero_le _
    | some k => exact (hpost y k).trans (Nat.le_add_left ..))
  exact ⟨endSafe.stopsWithin outcome (fun _ _ h => h.1), fun _ _ path =>
    endSafe.reach outcome (fun _ _ h => h.2) path⟩

end EvaluatorProgramMonomial

end VPVNP
end Computability
end OAI
