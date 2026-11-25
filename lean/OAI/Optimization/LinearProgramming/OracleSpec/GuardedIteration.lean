import OAI.Optimization.LinearProgramming.OracleSpec.PolynomialFuel

/-! An input-dependent bound on reachable intermediate words suffices: the physical
program checks the cap before running another elementary state transition. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace Fuel
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

variable {S I : Type}

private def guardStep {S : Type*} (es : S → List Bool) (f : S → S) (s : ℕ × S) : ℕ × S :=
  if (es s.2).length ≤ s.1 then (s.1,f s.2) else s

private noncomputable def guardProc {es : S → List Bool} {f : S → S} (p : Procedure es es f) :
    Procedure (prodCode unaryCode es) (prodCode unaryCode es) (guardStep es f) := by
  let cap := first unaryCode es
  let s := second unaryCode es
  let within := unaryLe.comp (((lengthInUnary es).comp s).pair cap)
  let advance := cap.pair (p.comp s)
  exact (conditional within advance (identity (prodCode unaryCode es))).congrFun (by
    intro x; simp [guardStep])

/-- Even from an arbitrary (possibly malformed) starting mathematical state, either the
transition is frozen or the next encoding length is bounded by the cap and the *existing*
finite procedure's time bound. -/
private theorem guard_bounded {es : S → List Bool} {f : S → S} (p : Procedure es es f)
    (s : ℕ × S) (i : ℕ) :
    let cur := ((guardStep es f)^[i]) s
    cur.1 = s.1 ∧ (es cur.2).length ≤ max (es s.2).length (s.1 + p.bound.eval s.1) := by
  induction i with
  | zero => exact ⟨rfl, Nat.le_max_left _ _⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    dsimp only at ih ⊢
    let t := ((guardStep es f)^[i]) s
    change (guardStep es f t).1 = s.1 ∧ (es (guardStep es f t).2).length ≤ _
    by_cases h : (es t.2).length ≤ t.1
    · have hb := p.output_length_le t.2
      have hP := Procedure.eval_nat_mono p.bound h
      have ht : t.1 = s.1 := ih.1
      refine ⟨by simpa [guardStep,h] using ht, ?_⟩
      rw [guardStep, ite_eq_left h]
      exact ((hb.trans (Nat.add_le_add h hP)).trans_eq (by rw [ht])).trans (Nat.le_max_right _ _)
    · simpa only [guardStep, ite_eq_right h] using ih

private noncomputable def globalSize (p : Polynomial ℕ) : Polynomial ℕ :=
  4*Polynomial.X + p + 2

private theorem guardSize {es : S → List Bool} {f : S → S} (p : Procedure es es f)
    (n : ℕ) (s : ℕ × S) (i : ℕ) :
    (prodCode unaryCode es (((guardStep es f)^[i]) s)).length ≤
      (globalSize p.bound).eval (n + (prodCode unaryCode es s).length) := by
  let x := n + (prodCode unaryCode es s).length
  let t := ((guardStep es f)^[i]) s
  obtain ⟨hcap,hsize⟩ := guard_bounded p s i
  have xeq : x = n + (2*s.1+(es s.2).length+1) := by simp [x,prodCode,pairBits_length,unaryCode]
  have h₁ : s.1 ≤ x := by omega
  have h₂ : (es s.2).length ≤ x := by omega
  have hp := Procedure.eval_nat_mono p.bound h₁
  change (prodCode unaryCode es t).length ≤ (globalSize p.bound).eval x
  simp only [globalSize, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat, prodCode, pairBits_length, unaryCode, List.length_replicate]
  change t.1 = s.1 at hcap
  change (es t.2).length ≤ _ at hsize
  have cap : t.1 ≤ x := hcap ▸ h₁
  have hp' : p.bound.eval s.1 ≤ p.bound.eval x := hp
  have hmax : max (es s.2).length (s.1+p.bound.eval s.1) ≤ x+p.bound.eval x :=
    max_le (h₂.trans (Nat.le_add_right _ _)) (Nat.add_le_add h₁ hp')
  have enc : (es t.2).length ≤ x + p.bound.eval x := hsize.trans hmax
  omega

private theorem guard_agrees (es : S → List Bool) (f : S → S) (s : S) (cap n : ℕ)
    (h : ∀ j < n, (es ((f^[j]) s)).length ≤ cap) :
    ((guardStep es f)^[n]) (cap,s) = (cap,(f^[n]) s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]
    simp [guardStep, h n (Nat.lt_succ_self _)]

/-- Compute both polynomials from the original input bit length, retain the cap, and
perform the requested number of work steps. Only words reached from `init x` before the
clock expires have to obey the source size invariant. -/
noncomputable def boundedReachable {ei : I → List Bool} {es : S → List Bool} {init : I → S} {step : S → S}
    (start : Procedure ei es init) (next : Procedure es es step) (ticks width : Polynomial ℕ)
    (hsize : ∀ x i, i < ticks.eval (ei x).length →
      (es ((step^[i]) (init x))).length ≤ width.eval (ei x).length) :
    Procedure ei es (fun x => (step^[ticks.eval (ei x).length]) (init x)) := by
  let prep := (clock ei width).pair start
  let loop := boundedIteration prep (guardProc next) ticks (globalSize next.bound)
    (fun n s i _ => guardSize next n s i)
  exact ((second unaryCode es).comp loop).congrFun (by
    intro x
    change (((guardStep es step)^[ticks.eval (ei x).length]) (width.eval (ei x).length,init x)).2 = _
    rw [guard_agrees _ _ _ _ _ (hsize x)])

end Fuel
end OracleSpec
end LinearProgramming
end Optimization
end OAI
