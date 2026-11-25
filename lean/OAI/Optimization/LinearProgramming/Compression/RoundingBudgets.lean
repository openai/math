import OAI.Optimization.LinearProgramming.Compression.AdaptiveRequests
import OAI.Optimization.LinearProgramming.Compression.ComputedEpoch
import OAI.Optimization.LinearProgramming.Games.StochasticPreprocessArithmetic
import OAI.Optimization.LinearProgramming.PriceGame.ControlWeightFolds

/-! ## Finite bit-stack programs constructing both exact sign budgets

The dimension and generator count are given as unary words. Every large value, including
factorials, powers, projection tests and the epoch sum, is constructed in binary. Only
exponents and summation indices are traversed as unary words. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RoundingBudgets

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Games.Stochastic.Preprocess (factorialP powerP)
open scoped BigOperators

variable {α : Type} {e : α → List Bool} {a b c : α → ℕ}

private abbrev B (e : α → List Bool) (a : α → ℕ) := Procedure e Nat.bits a
private abbrev U (e : α → List Bool) (a : α → ℕ) := Procedure e unaryCode a

private noncomputable abbrev bconst (e : α → List Bool) (n : ℕ) : B e (fun _ => n) := constant e Nat.bits n
private noncomputable abbrev uconst (e : α → List Bool) (n : ℕ) : U e (fun _ => n) := constant e unaryCode n
private noncomputable abbrev badd (p : B e a) (q : B e b) : B e (fun x => a x + b x) := binaryAdd.comp (p.pair q)
private noncomputable abbrev bmul (p : B e a) (q : B e b) : B e (fun x => a x * b x) := binaryMul.comp (p.pair q)
private noncomputable abbrev uadd (p : U e a) (q : U e b) : U e (fun x => a x + b x) := unaryAdd.comp (p.pair q)
private noncomputable abbrev umul (p : U e a) (q : U e b) : U e (fun x => a x * b x) := unaryMul.comp (p.pair q)
private noncomputable abbrev bits (p : U e a) : B e a := unaryToBits.comp p
private noncomputable abbrev bpow (p : B e a) (q : U e b) : B e (fun x => a x ^ b x) := powerP.comp (q.pair p)

private noncomputable def upow (p : U e a) (k : ℕ) : U e (fun x => a x ^ k) := by
  induction k with
  | zero => exact (uconst e 1).congrFun (fun x => (pow_zero (a x)).symm)
  | succ k ih => exact (umul ih p).congrFun (fun x => (pow_succ (a x) k).symm)

private noncomputable def bmax (p : B e a) (q : B e b) : B e (fun x => max (a x) (b x)) :=
  (conditional (binaryLt.comp (p.pair q)) q p).congrFun (by
    intro x
    change (if decide (a x < b x) then b x else a x) = max (a x) (b x)
    by_cases h : a x < b x
    · simp [h,max_eq_right h.le]
    · simp [h,max_eq_left (le_of_not_gt h)])

private noncomputable def cutoff (d : U e a) : B e (fun x => requestCutoff (a x)) :=
  bmul (bpow (bconst e 2) (uadd d (uconst e 2))) (badd (bits d) (bconst e 3))

/-- Exact radius of the first rounding invocation after obtaining a new minor request. -/
noncomputable def requestBudgetP : Procedure unaryCode Nat.bits
    (fun g : ℕ => (g+3)*(requestCutoff (g+1)+3)) := by
  let g := identity unaryCode
  exact bmul (badd (bits g) (bconst _ 3)) (badd (cutoff (uadd g (uconst _ 1))) (bconst _ 3))

private noncomputable def radius (n : U e a) : U e (fun x => paperRadius (a x)) :=
  umul (uconst e 100) (upow (uadd n (uconst e 1)) 3)

private noncomputable def width (n : U e a) : U e (fun x => paperWidth (a x)) := upow (uadd n (uconst e 1)) 6

private noncomputable def height (n : U e a) (g : U e b) : B e (fun x => epochHeightFor (a x) (b x)) := by
  let r := radius n
  let grid := bpow (bconst e 2) (uadd r (uconst e 7))
  let h := bmax (bmul (cutoff (uadd g (uconst e 1))) grid) (bmul (bconst e 2) grid)
  exact bmul (badd (badd (bits r) (bconst e 17)) (bmul (bconst e 4) h)) (bmul grid (bpow h (uconst e 4)))

private noncomputable def proj (d : U e a) (g : U e b) (H : B e c) : B e
    (fun x => projectionCoefficientBound (a x) (clearedProjectionRowBound (b x) (a x) (c x))) := by
  let row := bpow H (uadd (uadd g d) (uconst e 2))
  let t := uadd d (uconst e 1)
  let sq := bpow (bmax (bconst e 1) row) (uconst e 2)
  let w := bmul (factorialP.comp t) (bpow (bmul (bits t) sq) t)
  exact bmul (bits t) (bmul (bpow w (uconst e 2)) row)

private theorem list_sum_range (n : ℕ) (f : ℕ → ℕ) : ((List.range n).map f).sum=∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]

private noncomputable def fiber (g : U e a) (w : U e b) (H : B e c) :
    B e (fun x => fiberProjectionBudget (a x) (b x) (c x)) := by
  let ctx := second unaryCode e
  let item := proj (first unaryCode e) (g.comp ctx) (H.comp ctx)
  let terms := tabulate (f := fun x i => projectionCoefficientBound i (clearedProjectionRowBound (a x) i (c x))) 0 item
  let rows := terms.comp ((uadd w (uconst e 1)).pair (identity e))
  exact (PriceGame.Control.Native.sumWeightScoresP.comp rows).congrFun (by intro x; exact list_sum_range _ _)

abbrev Inputs := ℕ × ℕ

def inputsCode : Inputs → List Bool := prodCode unaryCode unaryCode

/-- Exact radius for the epoch commitment calculation, including every completion dimension. -/
noncomputable def epochBudgetP : Procedure inputsCode Nat.bits
    (fun x : Inputs => epochFormBudget x.2 (paperWidth x.1) (epochHeightFor x.1 x.2)) := by
  let n := first unaryCode unaryCode
  let g := second unaryCode unaryCode
  let all := fiber g (width n) (height n g)
  exact badd (bmul (badd (bits g) (bconst _ 1)) all) (bconst _ 1)

/-- The two exact argument packets for the scalar sign driver contain a unary
coordinate count and a binary radius. -/
noncomputable def epochInputP : Procedure inputsCode (prodCode unaryCode Nat.bits)
    (fun x : Inputs => (x.2+1,epochFormBudget x.2 (paperWidth x.1) (epochHeightFor x.1 x.2))) :=
  (uadd (second unaryCode unaryCode) (uconst _ 1)).pair epochBudgetP

noncomputable def requestInputP : Procedure inputsCode (prodCode unaryCode Nat.bits)
    (fun x : Inputs => (x.2+2,(x.2+3)*(requestCutoff (x.2+1)+3))) :=
  (uadd (second unaryCode unaryCode) (uconst _ 2)).pair (requestBudgetP.comp (second unaryCode unaryCode))

/-- The exact common denominator used by the request-offset and clipping grids. -/
noncomputable def gridP : Procedure unaryCode Nat.bits paperGrid :=
  bpow (bconst _ 2) (uadd (radius (identity unaryCode)) (uconst _ 7))

noncomputable def gridInputP : Procedure inputsCode Nat.bits (fun x : Inputs => paperGrid x.1) :=
  gridP.comp (first unaryCode unaryCode)

def values (n g : ℕ) : ℕ × ℕ := ((g+3)*(requestCutoff (g+1)+3),
  epochFormBudget g (paperWidth n) (epochHeightFor n g))

/-- The full preparation of the two call arguments is one physically polynomial procedure. -/
noncomputable def both : Procedure inputsCode (prodCode Nat.bits Nat.bits)
    (fun x : Inputs => values x.1 x.2) :=
  (requestBudgetP.comp (second unaryCode unaryCode)).pair epochBudgetP

/-- The actual finite stack program produces both binary integers. Its primitive clock
and both output lengths have an explicit polynomial in the supplied unary dimensions. -/
theorem run_and_word_bound (n g : ℕ) : ∃ c, c ≤ both.bound.eval (2*n+g+1) ∧
    @Runs both.K both.decideK both.program
      (@singletonStore both.K both.decideK both.input (inputsCode (n,g)))
      (@singletonStore both.K both.decideK both.output (prodCode Nat.bits Nat.bits (values n g))) c ∧
    (values n g).1.bits.length+(values n g).2.bits.length ≤ 2*n+g+1+both.bound.eval (2*n+g+1) := by
  have hlen : (inputsCode (n,g)).length=2*n+g+1 := by simp [inputsCode,prodCode,pairBits_length,unaryCode]
  obtain ⟨c,hc,hr⟩ := both.runs (n,g)
  have ho := both.output_length_le (n,g)
  rw [hlen] at hc ho
  simp only [prodCode,pairBits_length] at ho
  exact ⟨c,hc,hr,by omega⟩

private noncomputable def widthInputBound : Polynomial ℕ := 2*Polynomial.X+(Polynomial.X+1)^6+1

/-- A single polynomial in the manuscript dimension dominates the physical work and
both output words throughout every admitted generator epoch. -/
noncomputable def budgetBound : Polynomial ℕ := widthInputBound+both.bound.comp widthInputBound

theorem run_under_width (n g : ℕ) (hg : g ≤ paperWidth n) :
    ∃ c, c ≤ budgetBound.eval n ∧
      @Runs both.K both.decideK both.program
        (@singletonStore both.K both.decideK both.input (inputsCode (n,g)))
        (@singletonStore both.K both.decideK both.output (prodCode Nat.bits Nat.bits (values n g))) c ∧
      (values n g).1.bits.length+(values n g).2.bits.length ≤ budgetBound.eval n := by
  obtain ⟨c,hc,run,hw⟩ := run_and_word_bound n g
  have hi : 2*n+g+1 ≤ widthInputBound.eval n := by
    change g ≤ (n+1)^6 at hg
    simpa [widthInputBound] using Nat.add_le_add_right (Nat.add_le_add_left hg (2*n)) 1
  have hsum : 2*n+g+1+both.bound.eval (2*n+g+1) ≤ budgetBound.eval n := by
    simpa only [budgetBound,Polynomial.eval_add,Polynomial.eval_comp] using
      Nat.add_le_add hi (eval_nat_mono both.bound hi)
  exact ⟨c,hc.trans ((Nat.le_add_left _ _).trans hsum),run,hw.trans hsum⟩

end RoundingBudgets
end Compression
end LinearProgramming
end Optimization
end OAI
