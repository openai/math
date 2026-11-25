import OAI.Optimization.LinearProgramming.PriceGame.FixedSharePopulationWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignWireCursor
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignWirePolynomial

/-! A uniform polynomial on the binary encoding of a campaign cursor, including
all completed rounds' retained probe histories and the current expert roster. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open Learning Campaign States.Mass TrialExecution ExactQuantumFactoring.BitStackProgram

private def cursorEnvelope {A : Type*} [Semiring A] (x t pool price budget : A) : A :=
  let pair := fun a b : A => 2*a+b+1
  let list := fun n w : A => n*(2*w+2)+1
  let row := list (2*x^2) (2*price+4)
  let probe := pair x (pair row (list x row))
  let prior := list (t*budget) probe
  pair x (pair x (pair x (pair t (pair t (pair pool (pair prior t))))))

private theorem eval_cursorEnvelope (x t p w b : Polynomial ℕ) (z : ℕ) :
    (cursorEnvelope x t p w b).eval z =
      cursorEnvelope (x.eval z) (t.eval z) (p.eval z) (w.eval z) (b.eval z) := by
  simp only [cursorEnvelope, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_one]

private noncomputable def cursorPlan (timeExponent budgetExponent probes : ℕ)
    (pool price : Polynomial ℕ) : Polynomial ℕ :=
  let x := Polynomial.X
  cursorEnvelope x (x^timeExponent) pool price (Polynomial.C probes*(2*x)^budgetExponent)

private theorem eval_cursorPlan (u k p x : ℕ) (pool price : Polynomial ℕ) :
    (cursorPlan u k p pool price).eval x =
      cursorEnvelope x (x^u) (pool.eval x) (price.eval x) (p*(2*x)^k) := by
  simp only [cursorPlan, eval_cursorEnvelope, Polynomial.eval_X, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat]

/-- A fixed polynomial bounding every public cursor in the campaign. -/
noncomputable def cursorPolynomial : Polynomial ℕ :=
  cursorPlan 300 602 Complexity.probes poolWordPolynomial pricePolynomial

private theorem cursorWidth_le_envelope (N R T x U P W B : ℕ)
    (hx : N+R.size+1 ≤ x) (hT : T ≤ U) (hp : poolWidth N R T ≤ P)
    (hw : campaignPriceBits N R T ≤ W) (hb : Pool.probeBudget N ≤ B) :
    cursorWidth N R T ≤ cursorEnvelope x U P W B := by
  have hN : N ≤ x := by omega
  have hR : R.size ≤ x := by omega
  have hD : depth N ≤ x := (Nat.succ_le_succ (Nat.log2_le_self N)).trans (by omega)
  simp only [cursorWidth, cursorEnvelope, priorLogWidth, probeWidth, probeBound, historyBound,
    rowBound, pairBound, listBound]
  gcongr

private theorem scaledPower_mono (c k N x : ℕ) (h : N ≤ x) :
    c*(2*N)^k ≤ c*(2*x)^k :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ h) _)

theorem cursorWidth_polynomial (N R T : ℕ) (hT : T ≤ (N+R.size+1)^300) :
    cursorWidth N R T ≤ cursorPolynomial.eval (N+R.size+1) := by
  rw [cursorPolynomial, eval_cursorPlan]
  exact cursorWidth_le_envelope N R T (N+R.size+1) _ _ _ _ le_rfl hT
    (poolWidth_polynomial N R T hT) (campaignPriceBits_polynomial N R T hT)
    (scaledPower_mono Complexity.probes 602 N (N+R.size+1) (by omega))

/-- After any number of completed rounds, the actual encoded cursor (including its
entire probe log) obeys the same fixed polynomial, for arbitrary reply histories. -/
theorem run_cursor_wire_polynomial {N : ℕ} (a : Fin N) (R T : ℕ)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool))
    (out : ℕ → RoundResult N)
    (hx : ∀ j : Fin T, out j.val =
      ((trialLoop (Pool.batch N R) (runRound R (fun es => marketSolverAtCommonWeightUnit es))
        T (Population.start (Pool.batch N R))).run reply history) j)
    (hT : T ≤ (N+R.size+1)^300) (t : ℕ) (ht : t ≤ T) :
    (campaignCursorCode (replayCursor a R T out t)).length ≤ cursorPolynomial.eval (N+R.size+1) :=
  (run_cursor_length a R T reply history out hx t ht).trans (cursorWidth_polynomial N R T hT)

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
