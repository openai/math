import OAI.Optimization.LinearProgramming.Lattice.BitGuarded
import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic

/-! A fixed descending column controller. Its row and column counters are binary. The
unary execution and width budgets can be supplied by the outer reducer. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

variable {S : Type}

abbrev SweepState (S : Type) := ℕ × (ℕ × S)

def sweepCode (es : S → List Bool) := prodCode Nat.bits (prodCode Nat.bits es)

def sweepStep (update : ℕ → ℕ → S → S) (v : SweepState S) : SweepState S :=
  if v.1 = 0 then v else (v.1-1, v.2.1, update (v.1-1) v.2.1 v.2.2)

/-- One binary decrementation and one indexed column update, unless the sweep has ended. -/
noncomputable def sweepStepP {es : S → List Bool} {update : ℕ → ℕ → S → S}
    (column : Procedure (prodCode (prodCode Nat.bits Nat.bits) es) es
      (fun v => update v.1.1 v.1.2 v.2)) : Procedure (sweepCode es) (sweepCode es) (sweepStep update) := by
  let cursor := first Nat.bits (prodCode Nat.bits es)
  let rest := second Nat.bits (prodCode Nat.bits es)
  let row := (first Nat.bits es).comp rest
  let state := (second Nat.bits es).comp rest
  let previous := binarySub.comp (cursor.pair (constant (sweepCode es) Nat.bits 1))
  let replacement := column.comp ((previous.pair row).pair state)
  let advance := previous.pair (row.pair replacement)
  let original := identity (sweepCode es)
  refine (((choose advance original).comp ((binaryZero.comp cursor).pair original)).congrFun ?_)
  intro v
  change (if decide (v.1 = 0) then v else (v.1-1,v.2.1,update (v.1-1) v.2.1 v.2.2)) = _
  by_cases hv : v.1=0 <;> simp [sweepStep,hv]

/-- Descending fold over exactly `j-1,…,0`. -/
def foldColumns (update : ℕ → ℕ → S → S) (k : ℕ) : ℕ → S → S
  | 0, s => s
  | j+1, s => foldColumns update k j (update j k s)

theorem sweepStep_after_all (update : ℕ → ℕ → S → S) (k j : ℕ) (s : S) :
    (sweepStep update)^[j] (j,k,s) = (0,k,foldColumns update k j s) := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    simpa only [sweepStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one,
      foldColumns] using ih (update j k s)

theorem sweepStep_after_budget (update : ℕ → ℕ → S → S) (k j t : ℕ) (s : S) (hj : j ≤ t) :
    (sweepStep update)^[t] (j,k,s) = (0,k,foldColumns update k j s) := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hj
  rw [hr, Nat.add_comm j, Function.iterate_add_apply, sweepStep_after_all]
  exact Function.iterate_fixed (by simp [sweepStep]) r

/-- The external cap is shared with the outer loop. `rounds` is obtained by an actual
unary procedure, such as counting the rows of a framed basis matrix. -/
def runSweep (es : S → List Bool) (update : ℕ → ℕ → S → S) (rounds : ℕ × S → ℕ)
    (x : ℕ × (ℕ × S)) : S :=
  (((cappedTransition (sweepCode es) (sweepStep update))^[rounds x.2] (x.1,x.2.1,x.2)).2).2.2

noncomputable def runSweepP {es : S → List Bool} {update : ℕ → ℕ → S → S}
    {rounds : ℕ × S → ℕ} (count : Procedure (prodCode Nat.bits es) unaryCode rounds)
    (column : Procedure (prodCode (prodCode Nat.bits Nat.bits) es) es
      (fun v => update v.1.1 v.1.2 v.2)) :
    Procedure (prodCode unaryCode (prodCode Nat.bits es)) es (runSweep es update rounds) := by
  let cap := first unaryCode (prodCode Nat.bits es)
  let frame := second unaryCode (prodCode Nat.bits es)
  let row := (first Nat.bits es).comp frame
  let start := cap.pair (row.pair frame)
  let advance := cappedTransitionP (sweepStepP column)
  let loop := advance.iterate (Polynomial.C 2 * Polynomial.X)
    (fun n a i _ => cappedTransition_growth (sweepCode es) (sweepStep update) n a i)
  let out := loop.comp ((count.comp frame).pair start)
  let cursor := (second unaryCode (sweepCode es)).comp out
  let rowState := (second Nat.bits (prodCode Nat.bits es)).comp cursor
  exact (second Nat.bits es).comp rowState

/-- The concrete program's return value is the indexed fold when the supplied budgets
cover the native trace and every candidate sweep frame. -/
theorem runSweep_exact (es : S → List Bool) (update : ℕ → ℕ → S → S) (rounds : ℕ × S → ℕ)
    (cap k : ℕ) (s : S) (htime : k ≤ rounds (k,s))
    (hspace : ∀ i, 0 < i → i ≤ rounds (k,s) →
      (sweepCode es ((sweepStep update)^[i] (k,k,s))).length ≤ cap) :
    runSweep es update rounds (cap,k,s) = foldColumns update k k s := by
  unfold runSweep
  rw [cappedTransition_iterate_exact (hfit := hspace), sweepStep_after_budget _ _ _ _ _ htime]

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
