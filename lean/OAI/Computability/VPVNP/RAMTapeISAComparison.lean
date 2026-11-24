import OAI.Computability.VPVNP.RAMTapeISAOperand
import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.RAMTapeWordComparison

/-!
# Register comparisons for the conditional-jump dispatcher

The two operands are copied into independent work stacks before the scan,
even if both names refer to the same register. The scan returns one Boolean
at work port zero and empties the rest of its scratch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

open TapeWord BurstRAM PrivateRAM

variable {r k w : ℕ}

private def comparisonPorts : ScanPort → Port r k
  | .left => .work 0
  | .right => .work 1
  | .tmp => .work 2
  | .out => .work 3

private theorem comparisonPorts_injective : Function.Injective (comparisonPorts (r := r) (k := k)) := by
  intro i j h
  cases i <;> cases j <;> first | rfl | exact False.elim (of_decide_eq_false rfl (Port.work.inj h))

private def testRoutine (op : Comparison.Op) : FiniteRoutine (Port r k) := FiniteRoutine.ofRoutine {
  entry := Comparison.State.scan (.left op.initial)
  code := fun
    | .done bit => .push (.work 0) bit none
    | q@(.scan _) => (Comparison.code op q).rename comparisonPorts some }

/-- Stage both operands, run the comparison, and return with one decision bit. -/
def compareRegs (op : Comparison.Op) (x y : Fin r) : FiniteRoutine (Port r k) :=
  ((loadOperand (.reg x) (.work 0)).followedBy (loadOperand (.reg y) (.work 1))).followedBy
    (testRoutine op)

theorem compareRegs_run (op : Comparison.Op) (x y : Fin r) (pub : Fin k → Word w)
    (persistent : Word w) (reg : Fin r → Word w) (log : WriteLog w) :
    (compareRegs op x y).Runs (20 * w + 10) (bank pub persistent reg log)
      (Function.update (bank pub persistent reg log) (.work 0) [op.eval (reg x) (reg y)]) := by
  let s := bank pub persistent reg log
  let s₁ := Function.update s (.work 0) (wordBits (reg x))
  let s₂ := Function.update s₁ (.work 1) (wordBits (reg y))
  have hx : (loadOperand (.reg x) (.work 0)).Runs (7*w+3) s s₁ := by
    simpa only [s, s₁, bank, List.length_nil, Nat.zero_add, length_wordBits] using
      loadOperand_runs (src := .reg x) (dst := .work 0) (by simp)
        (by simp [copySafe]) (by simp [copySafe]) s rfl rfl
  have hy : (loadOperand (.reg y) (.work 1)).Runs (7*w+3) s₁ s₂ := by
    have h := loadOperand_runs (src := .reg y) (dst := .work 1) (by simp)
      (by simp [copySafe]) (by simp [copySafe]) s₁ (by rfl) (by rfl)
    change (loadOperand _ _).Runs (0 + 7 * (wordBits (reg y)).length + 3) s₁ s₂ at h
    simpa only [length_wordBits, Nat.zero_add] using h
  let kernel := testRoutine (r := r) (k := k) op
  let flag := op.eval (reg x) (reg y)
  have rows (q : Comparison.State) (hq : (Comparison.code op q).returns = false) :
      kernel.body.standalone (some q) = (Comparison.code op q).rename comparisonPorts some := by
    cases q with
    | scan => rfl
    | done => contradiction
  have scan := (Comparison.word_run op (reg x) (reg y)).lift comparisonPorts
    comparisonPorts_injective some s rows
  have hin : installStacks comparisonPorts s (scanStacks (wordBits (reg x)) (wordBits (reg y)) [] []) =
      s₂ := by
    apply installStacks_frame comparisonPorts_injective
    · intro i
      cases i <;> rfl
    · intro j hj
      exact (Function.update_of_ne (Ne.symm (hj .right)) ..).trans
        (Function.update_of_ne (Ne.symm (hj .left)) ..)
  have hout : installStacks comparisonPorts s (scanStacks [] [] [] []) = s :=
    installStacks_eq comparisonPorts_injective s _ (fun i => by cases i <;> rfl)
  rw [hin, hout] at scan
  have push : StackRuns kernel.body.standalone 1 (some (.done flag)) s none
      (Function.update s (.work 0) [flag]) := .cons (.push rfl) (.nil ..)
  have test : kernel.Runs ((6*w+3)+1) s₂ (Function.update s (.work 0) [flag]) := scan.trans push
  rw [show 20 * w + 10 = (7*w+3 + (7*w+3)) + ((6*w+3)+1) by omega]
  exact FiniteRoutine.Runs.followedBy (FiniteRoutine.Runs.followedBy hx hy) test

end RAMTape.ISA

end VPVNP
end Computability
end OAI
