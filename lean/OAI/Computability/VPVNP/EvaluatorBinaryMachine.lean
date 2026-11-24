import OAI.Computability.VPVNP.EvaluatorProgramMonomial
import OAI.Computability.VPVNP.EvaluatorScheduleCount
import OAI.Computability.VPVNP.RAMTapeSpaceNamed

/-!
# Binary machine for matrix-index evaluation

The input reader, radix converter, digit scheduler and terminal residue test
are linked in finite control. Only the two matrix callbacks vary when the
program is constructed. The tape table itself is independent of the advice
and the exponent width. Its two callbacks implement the scalar coordinate
queries and multiplication in the advised field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.BinaryMachine

open RAMTape EvaluatorDigitFetch EvaluatorProgramMonomial EvaluatorProgramRawInput
  EvaluatorMonomialSchedule EvaluatorRoutine EvaluatorScheduleEffects

variable {P : Type} [DecidableEq P]

/-- The binary evaluator's stack ports. The extra port holds the raw input, and the remaining
ports belong to the input converter and scheduler. -/
abbrev MachinePort (P : Type) := Option (EvaluatorProgramInput.Port P)

/-- Embed the three terminal registers into the scheduler's work bank. -/
def outputPorts (out : Output.Port → P) (k : Output.Port) : MachinePort P :=
  some (.sched (.work (out k)))

/-- Run the raw binary monomial program, then test its final endpoint and
branch directly on the low limb of the accumulated product. -/
def evaluator (ps : List P) (out : Output.Port → P) (frobenius multiply : FiniteRoutine (Port P)) :
    FiniteRoutine (MachinePort P) :=
  (rawMachine ps frobenius multiply).followedBy
    ((FiniteRoutine.ofRoutine Output.routine).onPorts (outputPorts out))

/-- The literal table of a fixed evaluator. Every input starts on its designated
raw input tape. -/
noncomputable def program [Fintype P] (ps : List P) (out : Output.Port → P)
    (frobenius multiply : FiniteRoutine (Port P)) : UniversalMachine.Program :=
  let r := (evaluator ps out frobenius multiply).body
  StackCompiler.labeledProgram none (r.close false) (some r.entry)

/-- A bound for every stack path transfers the integer count to the fixed
literal table. The overhead is quadratic in the bit-stack time and input size. -/
theorem program_paths_eq [Fintype P] (ps : List P) (out : Output.Port → P)
    (f m : FiniteRoutine (Port P)) (raw : List Bool) (T ticks : ℕ)
    (stops : let r := (evaluator ps out f m).body
      StopsWithin (r.close false) T (some r.entry) (StackCompiler.labeledInput none raw))
    (hclock : T * (6 * (raw.length + (Fintype.card (MachinePort P) + 1) + T) + 4) ≤ ticks) :
    let E := program ps out f m
    let r := (evaluator ps out f m).body
    UniversalMachine.paths E ticks (UniversalMachine.initial E raw) =
      stackPaths (r.close false) T (some r.entry) (StackCompiler.labeledInput none raw) :=
  StackCompiler.input_count_labeled none _ _ _ T ticks stops hclock

/-- A reachable bank size bound limits each literal tape head throughout
the evaluator computation, independently of the number of transitions. -/
theorem program_head_space [Fintype P] (ps : List P) (out : Output.Port → P)
    (f m : FiniteRoutine (Port P)) (raw : List Bool) {M : ℕ}
    (bounded : let r := (evaluator ps out f m).body
      ∀ ⦃q s⦄, StackCompiler.Reach (r.close false) (some r.entry) (StackCompiler.labeledInput none raw) q s →
        Fintype.card (MachinePort P)+1 + ∑ k, (s k).length ≤ M) (bits : List Bool) :
    let E := program ps out f m
    let d := choiceDisplacement E (UniversalMachine.initial E raw) bits
    StackCompiler.HeadBox (7*M+4) d.1 d.2 :=
  StackCompiler.input_space_labeled none _ _ _ bounded bits

variable {n p t Z v w : ℕ} [Fact p.Prime] {K A : Type}
    [Field K] [Fintype K] [Algebra (ZMod p) K] [CommRing A] [Algebra K A]
    [Algebra (ZMod p) A] [IsScalarTower (ZMod p) K A]

variable (b : Module.Basis (Fin n) K A) (u : Fin n) (coord : K →ₗ[ZMod p] ZMod p)
    (X : Fin t → A) (e : Fin t → BurstRAM.Word Z) (d : List Bool)
    (payload : Fin n × K → Stacks P) (out : Output.Port → P)
    (frobenius multiply : FiniteRoutine (Port P)) (BF BM : ℕ) (ps : List P)

local notation "data" => EvaluatorRadixRows.packedTable d.length (TapeWord.value d) (List.ofFn e)
local notation "next" => nextIndex b X
local notation "tape" => advice ps t d (payload (u,1)) ++ runtime e

/-- The actual stack-path count modulo the advised prime, given the two
matrix-step specifications. Output data are the binary current ordinal,
unary working limb width, and the packed field product beginning with its
prime-field coordinate. -/
theorem stackCount_mod (hp : ps.Nodup) (hall : ∀ a, a ∈ ps)
    (hout : Function.Injective out) (hunit : b u = 1) (hu : u.val = 0) (hdim : n ≤ 2 ^ v)
    (hw : SliceArithmetic.Word.workingWidth p ≤ w)
    (hd : TapeWord.value d = Fintype.card K)
    (hdata : ∀ s : Fin n × K, ∃ tail, (payload s) ∘ out =
      Output.bank (BurstRAM.wordBits (Fin.castLE hdim s.1 : BurstRAM.Word v)) (List.replicate w true)
        (BurstRAM.wordBits (SliceArithmetic.Word.limb w (⟨(coord s.2).val, ZMod.val_lt _⟩ : Fin p)) ++ tail))
    (R : ℕ) (hR : ∀ s, readTicks ps e d (payload s) ≤ R)
    (hf : ∀ (j : Fin Z) left, Realizes frobenius.body
      (fun x => bank data t Z d.length 0 j 0 left (payload x))
      (fun x => bank data t Z d.length 0 j 0 left (payload x)) BF (stepEffect next none))
    (hm : LabelCallback e d.length (TapeWord.value d) BM payload next multiply)
    (fuel : ℕ) (ht : 3*w+3+v + (R + (EvaluatorProgramInput.convertTicks t Z d.length +
      budget t Z d.length (TapeWord.value d) BF BM)) ≤ fuel) :
    let r := (evaluator ps out frobenius multiply).body
    (stackPaths (r.close false) fuel (some r.entry) (StackCompiler.labeledInput none tape) : ZMod p) =
      primeFunctional b u coord (∏ i, X i ^ (e i).val) := by
  have hq : 2 ≤ TapeWord.value d := hd ▸ Fintype.one_lt_card (α := K)
  have hrun := raw_realizes e d payload next frobenius multiply BF BM ps hp hall R hR hq hf hm
  let result := (FiniteRoutine.ofRoutine Output.routine).onPorts (outputPorts out)
  let post (s : Fin n × K) := InputBank.frame [] (EvaluatorProgramInput.extend Z d
    (bank data t Z d.length 0 0 0 0 (payload s)))
  let c (n : ℕ) (_ : Stacks (MachinePort P)) := if n = 0 then 0 else false.toNat
  have hpost (s : Fin n × K) (k : ℕ) (hk : 3*w+3+v ≤ k) :
      result.body.count c k (post s) = finishWeight u coord s := by
    have hpo : Function.Injective (outputPorts out) := fun _ _ h ↦
      hout (Port.work.inj (EvaluatorProgramInput.Port.sched.inj (Option.some_inj.mp h)))
    rw [show result = _ from rfl, FiniteRoutine.count_onPorts _ _ hpo]
    obtain ⟨tail, htail⟩ := hdata s
    change Output.routine.count _ _ (payload s ∘ out) = _
    rw [htail, show k = k - (3*w+3+v) + (3*w+3) + v by omega,
      Output.count_output_limb hw]
    have hz : (s.1.val = 0) ↔ s.1 = u := by rw [← hu, Fin.val_inj]
    simp only [Fin.val_castLE, hz, finishWeight]
  have hcount := hrun (3*w+3+v) fuel ht (u,1) (finishWeight u coord)
    (result.body.count c) hpost
  change (stackPaths _ fuel _ _ : ZMod p) = _
  rw [Routine.stackPaths_close]
  change ((evaluator ps out frobenius multiply).body.count c fuel _ : ZMod p) = _
  have heq : StackCompiler.labeledInput (none : MachinePort P) tape = InputBank.frame tape (fun _ ↦ []) := by
    funext k
    cases k <;> rfl
  rw [heq]
  have hseq := Routine.count_followedBy (rawMachine ps frobenius multiply).body result.body c fuel
    (InputBank.frame tape (fun _ ↦ []))
  have hnat := hseq.trans hcount
  rw [hd] at hnat
  exact (congrArg (fun z : ℕ ↦ (z : ZMod p)) hnat).trans (schedulerEffect_mod b u coord hunit X e)

end Evaluator.BinaryMachine

end VPVNP
end Computability
end OAI
