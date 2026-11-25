import OAI.Computability.BorderVNP.TeamClockedProgram
import OAI.Computability.BorderVNP.FiniteOutput

/-! # Field weights of elementary stack executions

A finite stack program may select its accepting weight from the final control
label. Counts of individual field values are recovered over the integers,
before reduction to the coefficient field. This transports the clock and
named-register proofs also in characteristic two.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldStack

open VPVNP.RAMTape VPVNP.UniversalMachine
open scoped BigOperators

variable {K Q F : Type*} [DecidableEq K] [Field F]

/-- Field-valued accepting leaves of the bounded stack computation. -/
def paths (c : StackCode K Q) (weight : Q → F) : ℕ → Q → Stacks K → F
  | 0, _, _ => 0
  | t+1, q, s => match c q with
    | .push k b r => paths c weight t r (Function.update s k (b :: s k))
    | .pop k f => paths c weight t (f (s k).head?) (Function.update s k (s k).tail)
    | .goto r => paths c weight t r s
    | .choose l r => paths c weight t l s + paths c weight t r s
    | .halt b => if b then weight q else 0

private def count (c : StackCode K Q) (test : Q → Bool) : ℕ → Q → Stacks K → ℕ
  | 0, _, _ => 0
  | t+1, q, s => match c q with
    | .push k b r => count c test t r (Function.update s k (b :: s k))
    | .pop k f => count c test t (f (s k).head?) (Function.update s k (s k).tail)
    | .goto r => count c test t r s
    | .choose l r => count c test t l s + count c test t r s
    | .halt b => (b && test q).toNat

private theorem sign_difference (c : StackCode K Q) (test : Q → Bool) (t : ℕ)
    (q : Q) (s : Stacks K) :
    TeamStack.paths c (fun _ => false) t q s - TeamStack.paths c test t q s =
      2 * (count c test t q s : ℤ) := by
  induction t generalizing q s with
  | zero => simp [TeamStack.paths, count]
  | succ t ih =>
    cases hc : c q with
    | push | pop | goto => simpa only [TeamStack.paths, count, hc] using ih _ _
    | choose l r =>
      simp only [TeamStack.paths, count, hc, Nat.cast_add]
      linarith only [ih l s, ih r s]
    | halt b => cases b <;> cases h : test q <;> simp [TeamStack.paths, count, hc, h, TeamTape.haltWeight]

private theorem paths_eq_count_sum [Fintype F] [DecidableEq F] (c : StackCode K Q) (w : Q → F)
    (t : ℕ) (q : Q) (s : Stacks K) :
    paths c w t q s = ∑ v : F, (count c (fun r => decide (w r = v)) t q s : F) * v := by
  induction t generalizing q s with
  | zero => simp [paths, count]
  | succ t ih =>
    cases hc : c q with
    | push | pop | goto => simpa only [paths, count, hc] using ih _ _
    | choose l r =>
      simp only [paths, count, hc, Nat.cast_add, add_mul, Finset.sum_add_distrib, ih]
    | halt b =>
      cases b <;> simp [paths, count, hc, Bool.toNat, ite_mul]

/-- Relabeling a stack bank and its finite control preserves the field value with
arbitrary accepting weights. -/
theorem paths_lift {L R : Type*} [DecidableEq L] {src : StackCode K Q} {target : StackCode L R}
    {w : Q → F} {w' : R → F} (ports : K → L) (hp : Function.Injective ports)
    (labels : Q → R) (base : Stacks L)
    (hc : ∀ q, target (labels q) = (src q).rename ports labels) (hv : ∀ q, w' (labels q) = w q)
    (t : ℕ) (q : Q) (s : Stacks K) :
    paths target w' t (labels q) (installStacks ports base s) = paths src w t q s := by
  induction t generalizing q s with
  | zero => rfl
  | succ t ih =>
    rw [paths, hc, paths]
    cases src q <;> simp only [StackOp.rename, Function.comp_apply, installStacks_at hp,
      installStacks_update hp, ih, hv]

variable {Port State : Type} [DecidableEq Port]

/-- Clock machinery returns zero at all its own states. The accepting source label
carries the original field weight. -/
def clockWeight (input : Port) (u : ℕ) (w : State → F) :
    (TeamClocked.startup input u).State ⊕ TeamGuard.Phase State → F
  | .inr (.execute q) => w q
  | _ => 0

/-- The named clock wrapper produces the genuine field-valued sum at the chosen
source fuel limit, even for malformed physical inputs. -/
theorem clock_value [Fintype F] (input : Port) (u : ℕ) (src : StackCode Port State)
    (w : State → F) (start : State) (raw : Word) :
    let T := 2 * raw.length^u + 2 + TeamClocked.prepSteps u raw.length
    let P := TeamClocked.code input u src start
    let q := Sum.inl (TeamClocked.startup input u).body.entry
    let s := StackCompiler.labeledInput (TeamClocked.Port.user input) raw
    paths P (clockWeight input u w) T q s =
      paths src w (raw.length^u) start (StackCompiler.labeledInput input raw) := by
  classical
  intro T P q s
  have test (neg : State → Bool) : TeamStack.paths P (TeamClocked.negative input u neg) T q s =
      TeamStack.paths src neg (raw.length^u) start (StackCompiler.labeledInput input raw) :=
    (TeamClocked.stack_run input u src neg start raw).2
  have hzero : TeamClocked.negative input u (fun _ : State => false) = fun _ => false := by
    funext z
    rcases z with _ | (_ | _ | _) <;> rfl
  rw [paths_eq_count_sum, paths_eq_count_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = 0
  · simp [hv]
  have hv' : 0 ≠ v := Ne.symm hv
  let neg := fun z => decide (w z = v)
  have hneg : TeamClocked.negative input u neg = fun z => decide (clockWeight input u w z = v) := by
    funext z
    rcases z with _ | (_ | _ | _) <;> simp [TeamClocked.negative, TeamGuard.negative, clockWeight, neg, hv']
    exact decide_eq_decide.mpr Iff.rfl
  have htotal := test (fun _ => false)
  rw [hzero] at htotal
  have htest := test neg
  rw [hneg] at htest
  have h₁ := sign_difference P (fun z => decide (clockWeight input u w z = v)) T q s
  have h₂ := sign_difference src neg (raw.length^u) start (StackCompiler.labeledInput input raw)
  have hcount : count P (fun z => decide (clockWeight input u w z = v)) T q s =
      count src neg (raw.length^u) start (StackCompiler.labeledInput input raw) := by omega
  rw [hcount]

end FieldStack

end BorderVNP
end Computability
end OAI
