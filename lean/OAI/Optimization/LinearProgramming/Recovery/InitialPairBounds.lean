import OAI.Optimization.LinearProgramming.Recovery.InitialPair
import OAI.Optimization.LinearProgramming.Compression.PolyEnvelope

/-! A single dimension-only operation polynomial covers the public LP loader and its
one-pass high transpose. The first independent-row request uses only the original
scalar encoding height and the constants 0 and 1. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialPair

open RAM RAM.Tape Geometry Polynomial
open scoped Matrix

private noncomputable def boxTable (rows cell : Polynomial ℕ) : Polynomial ℕ :=
  rows*(rows*(cell+rows*(4*rows+5)+4*rows+6+3)+5)+2

private theorem boxTable_eval (rows cell : Polynomial ℕ) (x : ℕ) :
    (boxTable rows cell).eval x = uniformTableTime (rows.eval x) (rows.eval x) (cell.eval x) := by
  simp [boxTable,uniformTableTime,uniformEntryTime]

noncomputable def stepPolynomial : Polynomial ℕ :=
  let dim : Polynomial ℕ := X+1
  let both : Polynomial ℕ := X+2
  let w : Polynomial ℕ := X*X+X
  let head : Polynomial ℕ := 256+w+w+both
  PublicInput.headers.budget + (7*w+1+1+boxTable dim (SlackRAM.cellPolynomial.comp dim)) +
    (headers.budget.comp head + boxTable dim (both*(4*both+5)+4*both+6))

theorem eval_le (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

private theorem table_le {r c b R C B : ℕ} (hr : r ≤ R) (hc : c ≤ C) (hb : b ≤ B) :
    uniformTableTime r c b ≤ uniformTableTime R C B := by
  unfold uniformTableTime uniformEntryTime
  gcongr

theorem stepBound_le (m d : ℕ) : stepBound m d ≤ stepPolynomial.eval (m+d) := by
  let x := m+d
  have rm : m+1 ≤ x+1 := by dsimp [x]; omega
  have cd : d+1 ≤ x+1 := by dsimp [x]; omega
  have mul : m*d ≤ x*x := Nat.mul_le_mul (by dsimp [x]; omega) (by dsimp [x]; omega)
  have words : PublicInput.words m d ≤ x*x+x := by unfold PublicInput.words; dsimp [x] at *; omega
  have both : d+1+(m+1) = x+2 := by dsimp [x]; omega
  have head : PublicInput.matrixBase m d+(d+1)+(m+1) ≤ 256+(x*x+x)+(x*x+x)+(x+2) := by
    unfold PublicInput.matrixBase PublicInput.sourceBase
    omega
  have p := table_le rm cd (le_refl (SlackRAM.cellPolynomial.eval (x+1)))
  have q := table_le cd rm (le_refl (readBound (d+1) (m+1)))
  have th := eval_le headers.budget head
  change stepBound m d ≤ stepPolynomial.eval x
  simp only [stepPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat,boxTable_eval]
  unfold stepBound transposeTime PublicInput.stepBound
  change PublicInput.headers.budget.eval x + (7*PublicInput.words m d+1+1+
    uniformTableTime (m+1) (d+1) (SlackRAM.cellPolynomial.eval (x+1))) +
    (headers.budget.eval (PublicInput.matrixBase m d+(d+1)+(m+1)) +
      uniformTableTime (d+1) (m+1) (readBound (d+1) (m+1))) ≤ _
  simp only [readBound,both] at q ⊢
  omega

theorem stepBound_monomial (m d : ℕ) :
    stepBound m d ≤ stepPolynomial.eval 1 * (m+d+1)^stepPolynomial.natDegree :=
  (stepBound_le m d).trans (Compression.polynomial_eval_le_monomial stepPolynomial (m+d))

/-- The public scalar bits at the first undecided pair are bounded directly by the
LP encoding. No later work-register height enters this estimate. -/
theorem program_rat_spec {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (B : ℕ)
    (input : ∀ k : ℕ, ratBits ((lpInput A b)[k]?.getD 0) ≤ B) :
    ∃ t c, c ≤ stepPolynomial.eval (m+d) ∧
      Block.Eval (Memory.AllData (fun q : ℚ => ratBits q ≤ max 3 B)) program
        (start [m,d] (lpInput A b)).memory c t ∧ Ready A b t ∧
      ∀ i j, ratBits ((slackColumns A b)ᵀ i j) ≤ max 3 B := by
  have z : ratBits (0 : ℚ) ≤ max 3 B := (by decide : ratBits (0 : ℚ) ≤ 3).trans (le_max_left _ _)
  have o : ratBits (1 : ℚ) ≤ max 3 B := (by decide : ratBits (1 : ℚ) ≤ 3).trans (le_max_left _ _)
  obtain ⟨t,c,hc,run,ready⟩ := program_spec A b (fun q => ratBits q ≤ max 3 B) z o
    (fun q hq => by simpa only [PrimalDual.ratBits_neg] using hq)
    (fun k => (input k).trans (le_max_right _ _))
  refine ⟨t,c,hc.trans (stepBound_le m d),run,ready,?_⟩
  intro i j
  have h : ratBits (uniformRect (d+1) (m+1) (t.index 202) t i j) ≤ max 3 B := run.safe_end _
  simpa only [ready.pairMatrix] using h

theorem tape_height {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (k : ℕ) :
    ratBits ((lpInput A b)[k]?.getD 0) ≤ max 3 (totalBits (lpInput A b)) := by
  cases h : (lpInput A b)[k]? with
  | none => exact (by decide : ratBits (0 : ℚ) ≤ 3).trans (le_max_left _ _)
  | some q =>
    exact (PrimalDual.ratBits_le_totalBits_of_mem (List.mem_of_getElem? h)).trans (le_max_right _ _)

/-- No separate input-height oracle is needed at public entry. -/
theorem program_tape_spec {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    let E := max 3 (totalBits (lpInput A b))
    ∃ t c, c ≤ stepPolynomial.eval (m+d) ∧
      Block.Eval (Memory.AllData (fun q : ℚ => ratBits q ≤ E)) program
        (start [m,d] (lpInput A b)).memory c t ∧ Ready A b t ∧
      ∀ i j, ratBits ((slackColumns A b)ᵀ i j) ≤ E := by
  have three : 3 ≤ max 3 (totalBits (lpInput A b)) := le_max_left _ _
  simpa only [max_eq_right three] using program_rat_spec A b _ (tape_height A b)

end InitialPair
end Recovery
end LinearProgramming
end Optimization
end OAI
