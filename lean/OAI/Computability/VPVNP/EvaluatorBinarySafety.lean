import OAI.Computability.VPVNP.EvaluatorBinaryMachine
import OAI.Computability.VPVNP.EvaluatorProgramInputBounds
import OAI.Computability.VPVNP.RAMTapeRoutineTotalPorts

/-!
# Stopping time and space for the complete binary evaluator

The raw input reader, radix converter, matrix callbacks and final residue
comparison execute as one finite stack routine. Both bounds cover rejected
paths as well as accepted paths. The terminal clock charges only the endpoint
and low-limb scans and adds no term involving the earlier running time to
the space estimate.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Routine

variable {K Q : Type*} [DecidableEq K]

/-- The same execution certifies every weaker pointwise storage condition. -/
theorem SafeFrom.weaken_space {r : Routine K Q} {safe safe' : Stacks K → Prop} {cont t q s}
    (h : r.SafeFrom safe cont t q s) (le : ∀ u, safe u → safe' u) : r.SafeFrom safe' cont t q s := by
  induction t generalizing q s with
  | zero => cases q <;> exact h
  | succ t ih =>
    cases q with
    | none => exact h
    | some q =>
      rw [SafeFrom] at h ⊢
      refine ⟨le s h.1, ?_⟩
      have next := h.2
      cases op : r.code q <;> rw [op] at next <;> first | exact ih next | exact ⟨ih next.1, ih next.2⟩ | trivial

end RAMTape.Routine

namespace Evaluator.BinaryMachine

open RAMTape EvaluatorRoutineSafety EvaluatorDigitFetch EvaluatorChronologicalLoop EvaluatorRadixRows
  EvaluatorMonomialSchedule EvaluatorProgramRawInput EvaluatorProgramMonomial

variable {P S : Type} [DecidableEq P] {t Z : ℕ}

/-- Time spent after the final matrix step. -/
def terminalTicks (v w : ℕ) := 3*w+3+v

/-- Instruction bound for the raw input reader, radix conversion, matrix schedule and final
endpoint and residue test together. -/
def fullTicks (t Z ℓ q A BF BM v w : ℕ) :=
  terminalTicks v w + (readerBudget t Z A + (EvaluatorProgramInput.convertTicks t Z ℓ + budget t Z ℓ q BF BM))

/-- Stack bound for all branches of the binary evaluator, including the storage used in its
final endpoint and residue scan. -/
def fullSpace (t Z ℓ workspace A v w : ℕ) := rawSpace t Z ℓ workspace A + terminalTicks v w

/-- The terminal scan preserves the separation between the singly exponential
input-length factor and the polynomial exponent-width factor of Theorem 8.1. -/
theorem fullTicks_le_exp_poly (t Z ℓ q A BF BM v w a k : ℕ)
    (ha : A ≤ 2^a) (ht : t ≤ 2^a) (hℓ : ℓ ≤ 2^a) (hq : q ≤ 2^a)
    (hM : BM ≤ 2^a*(Z+1)^k) (hF : BF ≤ 2^a*(Z+1)^k) (hv : v ≤ 2^a) (hw : w ≤ 2^a) :
    fullTicks t Z ℓ q A BF BM v w ≤ 2^(3*a+9)*(Z+1)^(k+2) := by
  have bound := parser_budget_le_exp_poly t Z ℓ q A BF BM a k ha ht hℓ hq hM hF
  have pos : 1 ≤ 2^a := Nat.two_pow_pos _
  have grow : 2^a ≤ 2^(3*a) := Nat.pow_le_pow_right (by decide) (by omega)
  have term : terminalTicks v w ≤ 2^(3*a+8) := by rw [pow_add]; unfold terminalTicks; norm_num; omega
  have hterm : terminalTicks v w ≤ 2^(3*a+8)*(Z+1)^(k+2) := term.trans (Nat.le_mul_of_pos_right (2^(3*a+8)) (Nat.pow_pos (n := k+2) (Nat.succ_pos Z)))
  apply (Nat.add_le_add hterm bound).trans_eq
  rw [show 3*a+9 = (3*a+8)+1 by omega, pow_succ 2 (3*a+8)]
  ring

/-- The space bound on the full machine is quartic in the numerical widths,
the label count, advice size and the space occupied by its callbacks. -/
theorem fullSpace_le_power (t Z ℓ workspace A v w : ℕ) :
    fullSpace t Z ℓ workspace A v w ≤ 157*(t+Z+ℓ+workspace+A+v+w+1)^4 := by
  let N := t+Z+ℓ+workspace+A+v+w+1
  have base := rawSpace_le_power t Z ℓ workspace A
  have hmono : (t+Z+ℓ+workspace+A+1)^4 ≤ N^4 := Nat.pow_le_pow_left (by dsimp [N]; omega) _
  have hpow : N ≤ N^4 := by
    have hn : 1 ≤ N := by dsimp [N]; omega
    simpa only [pow_one] using Nat.pow_le_pow_right hn (by decide : 1 ≤ 4)
  have hterm : terminalTicks v w ≤ 7*N := by dsimp [terminalTicks, N]; omega
  change rawSpace t Z ℓ workspace A + terminalTicks v w ≤ 157*N^4
  omega

private theorem output_safe (out : Output.Port → P) (ho : Function.Injective out) (s : Stacks (MachinePort P))
    (v w rawCap fuel : ℕ) (hs : stackFits rawCap s) (hidx : (s (outputPorts out .index)).length = v)
    (hwidth : (s (outputPorts out .width)).length = w) (hf : terminalTicks v w ≤ fuel) :
    ((FiniteRoutine.ofRoutine Output.routine).onPorts (outputPorts out)).body.Safe
      (stackFits (rawCap+terminalTicks v w)) (fun _ _ => False) fuel s := by
  let terminal := (FiniteRoutine.ofRoutine Output.routine).onPorts (outputPorts out)
  have inj : Function.Injective (outputPorts out) := fun _ _ h => ho (Port.work.inj
    (EvaluatorProgramInput.Port.sched.inj (Option.some.inj h)))
  have stop (cont : ℕ → Stacks (MachinePort P) → Prop) :
      terminal.body.AllStops cont (terminalTicks v w) s := by
    rw [show terminal = _ from rfl, FiniteRoutine.allStops_onPorts _ _ inj]
    let data := s ∘ outputPorts out
    have he : data = Output.bank (data .index) (data .width) (data .product) := by
      funext i; cases i <;> rfl
    have h := Output.allStops_output (data .index) (data .width) (data .product)
      (fun t a => cont t (installStacks (outputPorts out) s a))
    rw [← he, show (data .index).length = v from hidx, show (data .width).length = w from hwidth] at h
    exact h
  have result := safe_of_allStops (r := terminal.body) (safe := stackFits (rawCap+terminalTicks v w))
    (fun _ _ => False) (fuel-terminalTicks v w) (stop (fun _ _ => False)) (fun u h k =>
      (h k).trans (Nat.add_le_add_right (hs k) _))
  simpa only [Nat.sub_add_cancel hf] using result

variable (e : Fin t → BurstRAM.Word Z) (d : List Bool) (payload : S → Stacks P)
  (workspace : ℕ) (hp : ∀ x p, (payload x p).length ≤ workspace)
  (frobenius multiply : FiniteRoutine (Port P)) (BF BM : ℕ)

local notation "data" => packedTable d.length (TapeWord.value d) (List.ofFn e)
local notation "post" => fun x => EvaluatorProgramInput.extend Z d (bank data t Z d.length 0 0 0 0 (payload x))
local notation "nativeTicks" => EvaluatorProgramInput.convertTicks t Z d.length + budget t Z d.length (TapeWord.value d) BF BM

include hp in
/-- All binary branches of the complete evaluator halt by the full clock.
Every reachable stack on that same program satisfies the polynomial height bound. -/
theorem full_space_clock (ps : List P) (hn : ps.Nodup) (hall : ∀ p, p ∈ ps) (A : ℕ)
    (ha : ∀ x, (advice ps t d (payload x)).length ≤ A)
    (native : Bounded (nativeMachine frobenius multiply).body (stackFits (nativeSpace t Z d.length workspace))
      (EvaluatorProgramInput.initial e d ∘ payload) post nativeTicks)
    (out : Output.Port → P) (ho : Function.Injective out) (v w : ℕ)
    (hidx : ∀ x, (payload x (out .index)).length = v)
    (hwidth : ∀ x, (payload x (out .width)).length = w) (outcome : Bool) (x : S) :
    let r := (evaluator ps out frobenius multiply).body
    let raw := advice ps t d (payload x) ++ runtime e
    let start := StackCompiler.labeledInput (none : MachinePort P) raw
    StopsWithin (r.close outcome) (fullTicks t Z d.length (TapeWord.value d) A BF BM v w) (some r.entry) start ∧
      ∀ ⦃q s⦄, StackCompiler.Reach (r.close outcome) (some r.entry) start q s →
        stackFits (fullSpace t Z d.length workspace A v w) s := by
  let raw := rawMachine ps frobenius multiply
  let terminal := (FiniteRoutine.ofRoutine Output.routine).onPorts (outputPorts out)
  let tape := advice ps t d (payload x) ++ runtime e
  let start : Stacks (MachinePort P) := InputBank.frame tape (fun _ => [])
  let limit := rawSpace t Z d.length workspace A
  let T := fullTicks t Z d.length (TapeWord.value d) A BF BM v w
  have endHeight (y : S) : stackFits limit (InputBank.frame [] ((post) y)) := by
    have hs : stackFits (nativeSpace t Z d.length workspace) ((post) y) := by
      apply extend_fits e d workspace
      intro k
      have h := bank_length data t Z d.length workspace payload hp (i := 0) (j := 0)
        (left := 0) (cols := 0) (by omega) (by omega) y k
      exact h.trans (by unfold schedulerSpace; omega)
    intro k
    cases k with
    | none => exact Nat.zero_le _
    | some k => exact (hs k).trans (Nat.le_add_left ..)
  have rawBound := raw_bounded_of_native e d payload workspace frobenius multiply BF BM ps hn hall A ha native
  have combined : (raw.body.followedBy terminal.body).Safe (stackFits (limit+terminalTicks v w))
      (fun _ _ => False) T start := by
    rw [Routine.safe_followedBy]
    have h := rawBound (terminalTicks v w) T le_rfl x
      (terminal.body.Safe (stackFits (limit+terminalTicks v w)) (fun _ _ => False))
      (fun y k hk => output_safe out ho _ v w limit k (endHeight y) (hidx y) (hwidth y) hk)
    exact h.weaken_space (fun s hs k => (hs k).trans (Nat.le_add_right ..))
  have he : StackCompiler.labeledInput (none : MachinePort P) tape = start := by
    funext k; cases k <;> rfl
  dsimp only
  change StopsWithin _ T _ (StackCompiler.labeledInput none tape) ∧
    ∀ ⦃q s⦄, StackCompiler.Reach _ _ (StackCompiler.labeledInput none tape) q s → _
  rw [he]
  exact ⟨combined.stopsWithin outcome (fun _ _ h => h.elim), fun _ _ path =>
    combined.reach outcome (fun _ _ h => h.elim) path⟩

end Evaluator.BinaryMachine

end VPVNP
end Computability
end OAI
