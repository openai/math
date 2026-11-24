import OAI.Computability.VPVNP.RankQueryStackCursor
import OAI.Computability.VPVNP.EvaluatorRadixSpace

/-!
# A reusable physical cursor for the rank scan

A scalar coefficient supplies one zero-test bit. The cursor reads that bit,
computes its next two indices, copies them into its input registers, and
emits a new loop marker. A zero marker stops the enclosing loop with the
rank in input register one. A one marker calls the scalar query again using
the updated indices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor.Registers

open Dispatch BurstRAM RAMTape TapeWord

/-- Number of cursor word registers, comprising eight inputs, six outputs, and the scratch
registers of the control program. -/
abbrev R := 14 + control.scratch
/-- Address of one of the eight input words in the rank cursor’s physical register file. -/
abbrev arg := Code.inReg control.scratch
/-- Address of one of the six output words produced by the rank cursor control program. -/
abbrev resultReg := Code.outReg control.scratch

/-- The cursor’s word-machine ports together with the flag stack for the zero test and loop
decision. -/
inductive Port where
  | isa (k : ISA.Port R 0) | flag
  deriving DecidableEq, Fintype

/-- Extend a word-machine stack bank with the supplied list of cursor flags. -/
def frame (s : Stacks (ISA.Port R 0)) (flags : List Bool) : Stacks Port
  | .isa k => s k
  | .flag => flags

variable {w : ℕ}

/-- Initial cursor stacks containing the persistent word, the specified register file, empty
machine scratch, and the supplied flag stack. -/
def bank (persistent : Word w) (rs : Regs R w) (flags : List Bool) :=
  frame (ISA.bank Fin.elim0 persistent rs []) flags

/-- The loop bit associated with a cursor state, true while coefficient queries continue and
false when the rank has been returned. -/
def continuing : State → Bool
  | .running _ _ => true
  | .done _ => false

/-- Input register zero is overwritten by the next test. Register three
retains the fixed column bound, and registers four through seven stay zero. -/
def Stores (rs : Regs R w) (Z u z : ℕ) : Prop :=
  ∀ i : Fin 8, i ≠ 0 → (rs (arg i)).val = input Z u z false i

private def setFlag (zero : Bool) : RegCode R := .lit (arg 0) zero.toNat

private def loadFlag : FiniteRoutine Port :=
  .ofRoutine (Routine.popCase .flag (Routine.halt false)
    (((setFlag false).compile).onPorts .isa).body (((setFlag true).compile).onPorts .isa).body)

private def roll : RegCode R := .seq (.copy (arg 1) (resultReg 1)) (.copy (arg 2) (resultReg 2))

private def emitFlag : FiniteRoutine Port := .ofRoutine
  (Routine.popCase (.isa (.work 0)) (Routine.halt false) (Routine.push .flag false) (Routine.push .flag true))

/-- One fixed step, independent of register width, rank bounds, or the
coefficient oracle. The two indices are ready for the next iteration. -/
def next : FiniteRoutine Port :=
  (((loadFlag.followedBy ((control.physical control.scratch).onPorts .isa)).followedBy
    (roll.compile.onPorts .isa)).followedBy
    ((ISA.compareRegs .eq (resultReg 0) (arg 4)).onPorts .isa)).followedBy emitFlag

/-- Step bound for one cursor update, including the zero-test input, control instructions,
index copies, and the next loop bit. -/
def clock (w : ℕ) :=
  (3 + (control.emitFields control.scratch (List.finRange 6)).length)*(100*(w+1)^2) + 20*w+13

theorem wordFactor_eq : control.wordFactor = 68 := by decide

theorem register_count : R = 78 := by decide

theorem clock_eq (w : ℕ) : clock w = 7300*(w+1)^2+20*w+13 := by
  have hs : (control.emitFields control.scratch (List.finRange 6)).length = 70 := by decide
  rw [clock, hs]
  ring

private theorem run_isa (r : Machine R) {t : ℕ} {s out : Stacks (ISA.Port R 0)} (flags : List Bool)
    (h : r.Runs t s out) : (r.onPorts .isa).Runs t (frame s flags) (frame out flags) := by
  apply r.runs_onPorts_framed (ports := Port.isa) (s := frame s flags) (u := frame out flags) (fun _ _ he => Port.isa.inj he) h
    (fun _ => rfl) (fun _ => rfl)
  intro p hp
  cases p with
  | isa k => exact (hp k rfl).elim
  | flag => rfl

private theorem load_runs (zero : Bool) (persistent : Word w) (rs : Regs R w) (tail : List Bool) :
    ∃ t ≤ 100*(w+1)^2+1, loadFlag.Runs t (bank persistent rs (zero :: tail))
      (bank persistent ((setFlag zero).exec rs) tail) := by
  obtain ⟨n,hn,hr⟩ := (setFlag zero).compile_runs Fin.elim0 persistent rs
  have hf := run_isa _ tail hr
  have hu : Function.update (bank persistent rs (zero::tail)) Port.flag tail = bank persistent rs tail := by
    funext k; cases k <;> rfl
  refine ⟨n+1, Nat.add_le_add_right (by simpa only [setFlag, RegCode.length, Nat.one_mul] using hn) 1, ?_⟩
  cases zero
  · apply Routine.runs_popCase_false Port.flag _ _ _ (s := bank persistent rs (false :: tail)) rfl
    rw [hu]; exact hf
  · apply Routine.runs_popCase_true Port.flag _ _ _ (s := bank persistent rs (true :: tail)) rfl
    rw [hu]; exact hf

private theorem emit_runs (persistent : Word w) (rs : Regs R w) (b : Bool) (tail : List Bool) :
    emitFlag.Runs 2 (frame (Function.update (ISA.bank Fin.elim0 persistent rs []) (.work 0) [b]) tail)
      (bank persistent rs (b::tail)) := by
  let s := frame (Function.update (ISA.bank Fin.elim0 persistent rs []) (.work 0) [b]) tail
  have hu : Function.update s (.isa (.work 0)) [] = bank persistent rs tail := by
    funext k
    cases k with
    | flag => rfl
    | isa p =>
      by_cases h : p = .work 0 <;> simp [s, bank, frame, h]; rfl
  have hf : Function.update (bank persistent rs tail) .flag (b :: bank persistent rs tail .flag) =
      bank persistent rs (b::tail) := by funext k; cases k <;> rfl
  have push := Routine.runs_push .flag b (bank persistent rs tail)
  rw [hf] at push
  cases b
  · apply Routine.runs_popCase_false (Port.isa (.work 0)) _ _ _ (s := s) (tail := []) rfl
    rw [hu]; exact push
  · apply Routine.runs_popCase_true (Port.isa (.work 0)) _ _ _ (s := s) (tail := []) rfl
    rw [hu]; exact push

private theorem arg_injective : Function.Injective arg := fun _ _ h => Fin.ext (congrArg (fun j : Fin R => j.val) h)

private theorem result_ne_arg (i : Fin 6) (j : Fin 8) : resultReg i ≠ arg j := by
  intro h
  have hv := congrArg Fin.val h
  change 8+i.val = j.val at hv
  omega

private theorem roll_result (rs : Regs R w) (i : Fin 6) : roll.exec rs (resultReg i) = rs (resultReg i) := by
  simp [roll, RegCode.exec, Function.update_of_ne (result_ne_arg i 1), Function.update_of_ne (result_ne_arg i 2)]

/-- The next flag and register bank exactly implement the abstract transition.
In the halting case the first index is the answer and the second is zero. -/
theorem next_runs {p : ℕ} (Z u z : ℕ) (zero : Bool) (persistent : Word w) (rs : Regs R w)
    (tail : List Bool) (hw : (p+1)*control.wordFactor ≤ w)
    (he : ∀ i, input Z u z zero i < 2^p) (hr : Stores rs Z u z) :
    let v := advance Z u z zero
    ∃ t ≤ clock w, ∃ out : Regs R w,
      next.Runs t (bank persistent rs (zero::tail)) (bank persistent out (continuing v :: tail)) ∧
      Stores out Z (v.words 1) (v.words 2) := by
  let loaded := (setFlag zero).exec rs
  let v := advance Z u z zero
  have hpow : p ≤ w := by
    have hn : 1 ≤ control.wordFactor := by decide
    exact (Nat.le_succ p).trans ((Nat.le_mul_of_pos_right _ hn).trans hw)
  have hload (i : Fin 8) : (loaded (arg i)).val = input Z u z zero i := by
    by_cases hi : i = 0
    · subst i
      change (Fin.ofNat (2^w) zero.toNat).val = zero.toNat
      exact Nat.mod_eq_of_lt ((he 0).trans_le (Nat.pow_le_pow_right (by decide) hpow))
    · rw [show loaded (arg i) = rs (arg i) from Function.update_of_ne (arg_injective.ne hi) .., hr i hi]
      fin_cases i <;> first | rfl | contradiction
  obtain ⟨a,ha,h₁⟩ := load_runs zero persistent rs tail
  obtain ⟨b,hb,mid,hm,keep,hout⟩ := control.physical_runs _ p le_rfl _ loaded hw he hload Fin.elim0 persistent
  have h₂ := run_isa _ tail hm
  have hmid (i : Fin 6) : (mid (resultReg i)).val = v.words i := (hout i).trans (congrFun (control_eq ..) i)
  obtain ⟨c,hc,hroll⟩ := roll.compile_runs Fin.elim0 persistent mid
  let out := roll.exec mid
  have h₃ := run_isa _ tail hroll
  have houtarg (i : Fin 8) : (out (arg i)).val = if i = 2 then v.words 2 else
      if i = 1 then v.words 1 else input Z u z zero i := by
    by_cases hi₂ : i = 2
    · subst i
      simp [out, roll, RegCode.exec, Function.update_of_ne (result_ne_arg 2 1), hmid]
    · by_cases hi₁ : i = 1
      · subst i
        simp [out, roll, RegCode.exec, arg_injective.eq_iff, hi₂, hmid]
      · simp [out, roll, RegCode.exec, arg_injective.eq_iff, hi₁, hi₂, keep, hload]
  have hs : Stores out Z (v.words 1) (v.words 2) := by
    intro i hi
    rw [houtarg]
    fin_cases i <;> first | rfl | contradiction
  let bit := Comparison.Op.eq.eval (out (resultReg 0)) (out (arg 4))
  have hbit : bit = continuing v := by
    have hz : (out (arg 4)).val = 0 := hs 4 (by decide)
    have htag : (out (resultReg 0)).val = v.words 0 := (congrArg Fin.val (roll_result mid 0)).trans (hmid 0)
    simp only [bit, Comparison.Op.eval, Fin.ext_iff, hz, htag]
    cases v <;> rfl
  have h₄ := run_isa _ tail (ISA.compareRegs_run Comparison.Op.eq (resultReg 0) (arg 4)
    Fin.elim0 persistent out [])
  have h₅ := emit_runs persistent out bit tail
  have hfull := (((h₁.followedBy h₂).followedBy h₃).followedBy h₄).followedBy h₅
  rw [hbit] at hfull
  refine ⟨_, ?_, out, hfull, hs⟩
  change c ≤ 2*(100*(w+1)^2) at hc
  unfold clock
  rw [Nat.add_mul]
  omega

/-- Place a legal cursor in registers at the start of a scan. Only the two
indices and the column bound need nonzero words. -/
def initial (Z u z : Word w) : Regs R w :=
  Function.update (Function.update (Function.update (fun _ => 0) (arg 1) u) (arg 2) z) (arg 3) Z

theorem initial_stores (Z u z : Word w) : Stores (initial Z u z) Z.val u.val z.val := by
  intro i hi
  fin_cases i <;> first | contradiction | simp [initial, arg_injective.eq_iff, input]

theorem bank_length (persistent : Word w) (rs : Regs R w) (flags : List Bool) (k : Port) :
    (bank persistent rs flags k).length ≤ max w flags.length := by
  cases k with
  | flag => exact Nat.le_max_right ..
  | isa p =>
    apply le_trans _ (Nat.le_max_left w flags.length)
    cases p with
    | reg i | pub i => exact (length_wordBits _).le
    | persistent => exact (length_wordBits _).le
    | work i => exact Nat.zero_le _
    | logPort k => cases k <;> exact Nat.zero_le _

/-- Every intermediate physical stack respects the same quadratic working
space allowance, even when an arbitrary flag tail is carried through. -/
theorem next_space {p : ℕ} (Z u z : ℕ) (zero : Bool) (persistent : Word w) (rs : Regs R w)
    (tail : List Bool) (hw : (p+1)*control.wordFactor ≤ w) (he : ∀ i, input Z u z zero i < 2^p)
    (hr : Stores rs Z u z) {n : ℕ} {q : Option next.State} {s : Stacks Port}
    (run : StackRuns next.body.standalone n (some next.body.entry) (bank persistent rs (zero::tail)) q s)
    (k : Port) : (s k).length ≤ max w (tail.length+1) + clock w := by
  obtain ⟨t,ht,_,hdone,_⟩ := next_runs Z u z zero persistent rs tail hw he hr
  have hn := EvaluatorRadixDivision.ticks_le_at_return hdone (by rfl) run
  exact (EvaluatorRadixDivision.run_length run k).trans
    (Nat.add_le_add (bank_length persistent rs (zero::tail) k) (hn.trans ht))

end RankQuery.Stack.Cursor.Registers

end VPVNP
end Computability
end OAI
