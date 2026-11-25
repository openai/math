import OAI.Computability.QuantumFactoring.BitStackGCD
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListLength
import OAI.Computability.QuantumFactoring.BitStackTabulate

/-! Count the bits of the real input, construct a fixed polynomial budget in unary, and
iterate a charged state transformer without asking for a clock as input or advice. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace Fuel

variable {α I S : Type}

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

private def work (xs ys : List Bool) : Store (Fin 2) := ![xs,ys]
private def tallyCode : Program (Fin 2) := .loop 0 (.push 1 true) (.push 1 true)

@[simp] private theorem read0 (xs ys : List Bool) : work xs ys 0 = xs := rfl
@[simp] private theorem read1 (xs ys : List Bool) : work xs ys 1 = ys := rfl
@[simp] private theorem write0 (xs ys z : List Bool) : Function.update (work xs ys) 0 z = work z ys := by
  funext i; fin_cases i <;> simp
@[simp] private theorem write1 (xs ys z : List Bool) : Function.update (work xs ys) 1 z = work xs z := by
  funext i; fin_cases i <;> simp

private theorem tally_runs (xs : List Bool) (n : ℕ) :
    Runs tallyCode (work xs (unaryCode n)) (work [] (unaryCode (n+xs.length))) (2*xs.length+1) := by
  induction xs generalizing n with
  | nil => simpa [tallyCode] using (Runs.loop_nil (k := (0 : Fin 2)) (p := Program.push 1 true)
      (q := Program.push 1 true) (s := work [] (unaryCode n)) rfl)
  | cons b bs ih =>
    have tail := ih (n+1)
    have body := Runs.push (work bs (unaryCode n)) 1 true
    simp only [read1, write1] at body
    change Runs _ _ (work bs (unaryCode (n+1))) 1 at body
    have hdst : n+(b::bs).length = n+1+bs.length := by simp; omega
    have htime : 2*(b::bs).length+1 = (2*bs.length+1)+1+1 := by simp; omega
    rw [hdst, htime]
    cases b with
    | false =>
      apply Runs.loop_false (k := (0 : Fin 2)) (p := Program.push 1 true) (q := Program.push 1 true)
        (s := work (false::bs) (unaryCode n)) (xs := bs) (a := 1) (b := 2*bs.length+1) rfl
      · simpa only [write0] using body
      · exact tail
    | true =>
      apply Runs.loop_true (k := (0 : Fin 2)) (p := Program.push 1 true) (q := Program.push 1 true)
        (s := work (true::bs) (unaryCode n)) (xs := bs) (a := 1) (b := 2*bs.length+1) rfl
      · simpa only [write0] using body
      · exact tail

/-- Unlike a host word-length primitive, this program inspects and consumes each input bit. -/
noncomputable def lengthInUnary (ea : α → List Bool) : Procedure ea unaryCode (fun a => (ea a).length) where
  K := Fin 2
  finiteK := inferInstance
  decideK := inferInstance
  input := 0
  output := 1
  program := tallyCode
  bound := 2*Polynomial.X+1
  runs a := by
    have before : work (ea a) [] = singletonStore 0 (ea a) := by
      funext i; fin_cases i <;> simp [singletonStore]
    have after : work [] (unaryCode (ea a).length) = singletonStore 1 (unaryCode (ea a).length) := by
      funext i; fin_cases i <;> simp [singletonStore]
    refine ⟨2*(ea a).length+1, by simp, ?_⟩
    simpa only [unaryCode, List.replicate_zero, Nat.zero_add, before, after] using tally_runs (ea a) 0

private noncomputable def power {ea : α → List Bool} {f : α → ℕ} (p : Procedure ea unaryCode f) :
    (k : ℕ) → Procedure ea unaryCode (fun a => f a ^ k)
  | 0 => (constant ea unaryCode 1).congrFun (by simp)
  | k+1 => (unaryMul.comp ((power p k).pair p)).congrFun (by intro a; simp [pow_succ])

/-- The polynomial determines the fixed finite program that computes the clock. -/
private theorem polynomial_exists {ea : α → List Bool} {f : α → ℕ} (p : Procedure ea unaryCode f)
    (q : Polynomial ℕ) : Nonempty (Procedure ea unaryCode (fun a => q.eval (f a))) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    obtain ⟨l⟩ := hq
    obtain ⟨r⟩ := hr
    exact ⟨(unaryAdd.comp (l.pair r)).congrFun (by intro a; simp)⟩
  | monomial k c =>
    exact ⟨(unaryMul.comp ((constant ea unaryCode c).pair (power p k))).congrFun
      (by intro a; simp)⟩

noncomputable def polynomial {ea : α → List Bool} {f : α → ℕ} (p : Procedure ea unaryCode f)
    (q : Polynomial ℕ) : Procedure ea unaryCode (fun a => q.eval (f a)) :=
  Classical.choice (polynomial_exists p q)

noncomputable def clock (ea : α → List Bool) (q : Polynomial ℕ) :
    Procedure ea unaryCode (fun a => q.eval (ea a).length) := polynomial (lengthInUnary ea) q

/-- Initialize a real work state, compute a unary fuel budget from the original bits, and
run that many *real* transitions. The size hypothesis bounds intermediate data under an
already implemented step. It asserts no machine implementation or correctness result. -/
noncomputable def boundedIteration {ei : I → List Bool} {es : S → List Bool} {init : I → S} {step : S → S}
    (start : Procedure ei es init) (next : Procedure es es step) (count size : Polynomial ℕ)
    (hsize : ∀ n s i, i ≤ n → (es ((step^[i]) s)).length ≤ size.eval (n + (es s).length)) :
    Procedure ei es (fun x => (step^[count.eval (ei x).length]) (init x)) :=
  (next.iterate size hsize).comp ((clock ei count).pair start)

/-- Once a halting configuration is absorbing, extra computed fuel has no effect. -/
theorem iterate_after_fixed {S : Type*} {f : S → S} {s t : S} {used budget : ℕ} (h : (f^[used]) s = t)
    (stop : f t = t) (enough : used ≤ budget) : (f^[budget]) s = t := by
  rw [← Nat.sub_add_cancel enough, Function.iterate_add_apply, h]
  exact Function.iterate_fixed stop _

end Fuel
end OracleSpec
end LinearProgramming
end Optimization
end OAI
