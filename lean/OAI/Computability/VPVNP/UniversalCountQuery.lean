import OAI.Computability.VPVNP.UniversalCountAdvice
import OAI.Computability.VPVNP.AdviceCountAdapter

/-!
# Executable coefficient queries for the universal path-count family

The coefficient query uses one fixed finite bit-stack control for all lengths.
Its only circuit-specific input is the unary-addressed gate stream. The final
binary count includes all and only accepting canonical choices. Both its width
and the maximum height of every intermediate stack are polynomial in the
length for the concrete coefficient verifier.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalCountStack

open RAMTape VerifierMachine
open AdviceCountAdapter (AuxPort verify)

/-- A fixed stack routine that enumerates all witnesses of the advised Boolean circuit and
returns their accepting count in binary. -/
abbrev countCircuit := enumerate verify.body

variable {u w g : ℕ}

/-- Instruction budget per candidate witness, including the ripple counters. -/
def perChoice (c : BooleanTranscript.Circuit (Fin u ⊕ Fin w) g) : ℕ :=
  32 * ((AdviceCircuit.encode (AdviceCircuit.compile c)).length + (AdviceCircuit.compile c).length +
    u + w + 1) + 8*w + 9

/-- Space per stack, measured at every instruction of the full count. -/
def stackLimit (c : BooleanTranscript.Circuit (Fin u ⊕ Fin w) g) : ℕ :=
  max (max u (AdviceCircuit.encode (AdviceCircuit.compile c)).length) (w+1) + perChoice c

/-- Install the advice and query, leaving the verifier's work ports empty. -/
def scalarInputs (c : BooleanTranscript.Circuit (Fin u ⊕ Fin w) g) (x : Fin u → Bool) : Stacks AuxPort :=
  AdviceCountAdapter.inputs (List.ofFn x) (AdviceCircuit.encode (AdviceCircuit.compile c))

/-- One uniform machine counts satisfying witnesses of any topologically ordered
Boolean circuit supplied on its advice port. Its control and number of stacks
are independent of all circuit parameters. -/
theorem countCircuit_runs (c : BooleanTranscript.Circuit (Fin u ⊕ Fin w) g) (x : Fin u → Bool) :
    ∃ t ≤ 2^w * perChoice c, SpaceRun countCircuit.standalone (stackLimit c) t
      (some countCircuit.entry) (bank (scalarInputs c x) (digits w 0) (digits (w+1) 0) [] []) none
      (bank (scalarInputs c x) (digits w 0) (digits (w+1) (∑ bits, (c.eval (Sum.elim x bits)).toNat)) [] []) := by
  let p := AdviceCircuit.compile c
  let a := AdviceCircuit.encode p
  let B := 32 * (a.length + p.length + u + w + 1)
  apply enumerate_runs (B := B) (A := max u a.length)
  · intro k
    cases k with
    | query => change (List.ofFn x).length ≤ max u a.length; simp
    | advice => exact le_max_right ..
    | vmStream | vmValues | vmScratch | vmResult | copyTmp => exact Nat.zero_le _
  · intro bits count _
    obtain ⟨tail, h⟩ := AdviceCircuit.compile_run c x bits
    obtain ⟨t, ht, hr⟩ := AdviceCountAdapter.verify_runs p (List.ofFn x) (List.ofFn bits) count h
    exact ⟨t, by simpa only [B, a, List.length_ofFn] using ht, hr⟩

private theorem sum_verifier_eval {n : ℕ} (x : Fin n → Bool) :
    (∑ bits, ((verifierCircuit n).eval (Sum.elim x bits)).toNat) = acceptingCount x := by
  have h := acceptingCount_eq_sum_witnesses (R := ℕ) x
  simp only [Nat.cast_id] at h
  rw [h]
  refine Finset.sum_congr rfl fun bits _ => ?_
  rw [verifierCircuit_eval]
  cases verifiesInput x bits <;> rfl

/-- The §8.1 constant-term oracle for the polynomial family (1.1), including
malformed input prefixes and early accepting halts. No interpreter assumptions
are required. The exact integer output is read by `count_digits_value`. -/
theorem coefficient_query_runs {n : ℕ} (x : Fin n → Bool) :
    ∃ t ≤ 2^(n^clockExponent) * perChoice (verifierCircuit n),
      SpaceRun countCircuit.standalone (stackLimit (verifierCircuit n)) t (some countCircuit.entry)
        (bank (scalarInputs (verifierCircuit n) x) (digits (n^clockExponent) 0)
          (digits (n^clockExponent+1) 0) [] []) none
        (bank (scalarInputs (verifierCircuit n) x) (digits (n^clockExponent) 0)
          (digits (n^clockExponent+1) (acceptingCount x)) [] []) := by
  simpa only [sum_verifier_eval] using countCircuit_runs (verifierCircuit n) x

private theorem perChoice_polynomial :
    PolynomiallyBounded (fun n => perChoice (verifierCircuit n)) := by
  have hsize := verifierProgram_advice_polynomial
  have ht := PolynomiallyBounded.id.pow clockExponent
  have hp := verifierSize_polynomiallyBounded.add (.const 2)
  simp only [perChoice, AdviceCircuit.compile_length]
  exact (((PolynomiallyBounded.const 32).mul
    ((((hsize.add hp).add .id).add ht).add (.const 1))).add ((PolynomiallyBounded.const 8).mul ht)).add (.const 9)

/-- The entire physical bit-stack bank uses polynomial space, since the
program has a fixed finite number of ports. -/
theorem coefficient_query_space :
    PolynomiallyBounded (fun n => stackLimit (verifierCircuit n)) := by
  have ht := PolynomiallyBounded.id.pow clockExponent
  have hsize := verifierProgram_advice_polynomial
  refine ((((PolynomiallyBounded.id.add hsize).add (ht.add (.const 1))).add perChoice_polynomial)).of_le ?_
  intro n
  dsimp only [stackLimit, verifierProgram]
  omega

/-- A single polynomial exponent bounds the entire running time over all query words. -/
theorem coefficient_query_time : ∃ e : ℕ → ℕ, PolynomiallyBounded e ∧ ∀ n,
    2^(n^clockExponent) * perChoice (verifierCircuit n) ≤ 2^(e n) := by
  refine ⟨_, (PolynomiallyBounded.id.pow clockExponent).add perChoice_polynomial, fun n => ?_⟩
  rw [pow_add]
  exact Nat.mul_le_mul_left _ (Nat.lt_pow_self (by decide : 1 < 2)).le

end UniversalCountStack

end VPVNP
end Computability
end OAI
