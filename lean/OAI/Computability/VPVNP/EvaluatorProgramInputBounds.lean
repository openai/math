import OAI.Computability.VPVNP.EvaluatorProgramRawSafety
import OAI.Computability.VPVNP.EvaluatorScheduleBudget
import OAI.Computability.VPVNP.PolynomialBounds

/-!
# Advice and clock bounds for the evaluator with its input parser

A fixed list of polynomial-length callback registers gives polynomial advice
for the whole program. The parser reads a runtime stream linear in the number
of exponent bits. Its cost fits the same exponential-in-length,
polynomial-in-exponent-width clock as conversion and traversal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorProgramRawInput

open RAMTape

variable {P : Type}

theorem advice_polynomiallyBounded (ps : List P) (t : ℕ → ℕ) (d : ℕ → List Bool)
    (payload : ℕ → Stacks P) (ht : PolynomiallyBounded t)
    (hd : PolynomiallyBounded fun n => (d n).length)
    (hp : ∀ p, PolynomiallyBounded fun n => (payload n p).length) :
    PolynomiallyBounded fun n => (advice ps (t n) (d n) (payload n)).length := by
  have fieldsBound (ks : List P) :
      PolynomiallyBounded fun n => (ks.map fun p => 2*(payload n p).length+1).sum := by
    induction ks with
    | nil => exact .const 0
    | cons p ks ih =>
      simpa only [List.map_cons, List.sum_cons] using
        ((((PolynomiallyBounded.const 2).mul (hp p)).add (.const 1)).add ih)
  simpa only [advice_length] using
    ((((PolynomiallyBounded.const 4).mul ht).add ((PolynomiallyBounded.const 4).mul hd)).add
      (.const 4)).add (fieldsBound ps)

/-- Add the parser clock to the full machine allowance. The exponent-array
width changes only the polynomial factor, and the bound is uniform over
binary inputs of that width and the index path. -/
theorem parser_budget_le_exp_poly (t Z ℓ Q A BF BM a k : ℕ)
    (ha : A ≤ 2^a) (ht : t ≤ 2^a) (hℓ : ℓ ≤ 2^a) (hQ : Q ≤ 2^a)
    (hM : BM ≤ 2^a*(Z+1)^k) (hF : BF ≤ 2^a*(Z+1)^k) :
    EvaluatorProgramMonomial.readerBudget t Z A + (EvaluatorProgramInput.convertTicks t Z ℓ +
      EvaluatorMonomialSchedule.budget t Z ℓ Q BF BM) ≤ 2^(3*a+8)*(Z+1)^(k+2) := by
  have hs := EvaluatorScheduleBudget.scheduleBudget_le_exp_poly t Z ℓ Q BM BF a k ht hℓ hQ hM hF
  change EvaluatorProgramInput.convertTicks t Z ℓ + EvaluatorMonomialSchedule.budget t Z ℓ Q BF BM ≤ _ at hs
  let E := 2^a
  have hE : 1 ≤ E := Nat.two_pow_pos a
  have htz : t*Z ≤ E*Z := Nat.mul_le_mul_right _ ht
  have hz : Z ≤ E*Z := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right Z hE
  have hr' : EvaluatorProgramMonomial.readerBudget t Z A ≤ 20*E*(Z+1) := by
    change A ≤ E at ha
    unfold EvaluatorProgramMonomial.readerBudget EvaluatorProgramMonomial.inputLengthBound
    rw [Nat.mul_succ, Nat.mul_assoc]
    omega
  have hcoef : 20*E ≤ 2^(3*a+7) := by
    calc
      20*E ≤ 128*2^(3*a) := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right (by decide) (by omega))
      _ = _ := by rw [pow_add, Nat.mul_comm]; rfl
  have hpow : Z+1 ≤ (Z+1)^(k+2) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos Z) (show 1 ≤ k+2 by omega)
  have hread := hr'.trans (Nat.mul_le_mul hcoef hpow)
  rw [show 3*a+8 = (3*a+7)+1 by omega, pow_succ]
  calc
    _ ≤ 2^(3*a+7)*(Z+1)^(k+2) + 2^(3*a+7)*(Z+1)^(k+2) := Nat.add_le_add hread hs
    _ = _ := by ring

/-- The exact reader cost on a given input is bounded by the same clock. -/
theorem parser_schedule_le_exp_poly {t Z a k BF BM : ℕ} (ps : List P)
    (e : Fin t → BurstRAM.Word Z) (d : List Bool) (payload : Stacks P)
    (ha : (advice ps t d payload).length ≤ 2^a)
    (ht : t ≤ 2^a) (hℓ : d.length ≤ 2^a) (hQ : TapeWord.value d ≤ 2^a)
    (hM : BM ≤ 2^a*(Z+1)^k) (hF : BF ≤ 2^a*(Z+1)^k) :
    readTicks ps e d payload + (EvaluatorProgramInput.convertTicks t Z d.length +
      EvaluatorMonomialSchedule.budget t Z d.length (TapeWord.value d) BF BM) ≤
        2^(3*a+8)*(Z+1)^(k+2) := by
  have hr := readTicks_le ps e d payload
  rw [runtime_length] at hr
  exact (Nat.add_le_add_right hr _).trans (parser_budget_le_exp_poly _ _ _ _ _ _ _ _ _ ha ht hℓ hQ hM hF)

end EvaluatorProgramRawInput

end VPVNP
end Computability
end OAI
