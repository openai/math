import OAI.Computability.NearSquareRoot.KernelPencilSearch

/-! # Action of the generated binary query pencil

The row indices split into the independent shift blocks and the clock register
within each block. At any frequency all queries are scalars, so iterating the
ordinary pencil uses the power of the single matrix certified by the search. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PencilSearch

open CyclotomicCode Matrix

variable {a m h b W : ℕ} {V ν : Type*} [AddCommGroup V] [Module (Number a) V]

/-- A stage of the fixed affine query pencil on globally numbered rows. -/
def indexedPencilStep (e : Signature m × Clock h b ≃ Fin W)
    (A : Coefficients a m h b) (Q : Fin m → Module.End (Number a) V)
    (x : Fin W → V) (i : Fin W) : V :=
  let (β, c) := e.symm i
  (∑ t, A β none c t • x (e (β, t))) +
    ∑ j, ∑ t, A β (some j) c t • Q j (x (e (β, t)))

/-- The ordinary-coordinate predictor consists of `b` successive pencil stages. -/
def indexedPredictor (e : Signature m × Clock h b ≃ Fin W)
    (A : Coefficients a m h b) (Q : Fin m → Module.End (Number a) V) :
    (Fin W → V) → Fin W → V := (indexedPencilStep e A Q)^[b]

variable (e : Signature m × Clock h b ≃ Fin W) (A : Coefficients a m h b)
    (S : V ≃ₗ[Number a] (ν → Number a)) (sig : ν → Signature m)
    (Q : Fin m → Module.End (Number a) V)
    (hQ : ∀ j v ω, S (Q j v) ω = sign a (sig ω j) * S v ω)

include hQ

private theorem step_at_frequency (x : Fin W → V) (β : Signature m) (c : Clock h b) (ω : ν) :
    S (indexedPencilStep e A Q x (e (β, c))) ω =
      (stage A (sig ω) β *ᵥ (fun t => S (x (e (β, t))) ω)) c := by
  simp only [stage, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec]
  simp [indexedPencilStep, Matrix.mulVec, dotProduct, Finset.sum_apply, hQ, Finset.mul_sum,
    mul_left_comm]

/-- On a shift block, the frequency coordinates of any prefix of the ordinary
pencil execution evolve by the corresponding matrix power. -/
theorem indexedPencilStep_iterate (n : ℕ) (x : Fin W → V) (β : Signature m) (ω : ν) :
    (fun c => S (((indexedPencilStep e A Q)^[n]) x (e (β, c))) ω) =
      stage A (sig ω) β ^ n *ᵥ (fun c => S (x (e (β, c))) ω) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext c
    rw [Function.iterate_succ_apply', step_at_frequency e A S sig Q hQ, ih,
      Matrix.mulVec_mulVec, pow_succ']

omit hQ

/-- The computed scalar applies separately to every original row regardless
of the shift/clock numbering. -/
theorem indexedPredictor_spectral [NeZero b] (e : Signature m × Clock h b ≃ Fin W)
    (A : Coefficients a m h b) (hA : Good A)
    (S : V ≃ₗ[Number a] (ν → Number a)) (sig : ν → Signature m)
    (Q : Fin m → Module.End (Number a) V)
    (hQ : ∀ j v ω, S (Q j v) ω = sign a (sig ω j) * S v ω)
    (x : Fin W → V) (i : Fin W) (ω : ν) :
    S (indexedPredictor e A Q x i) ω =
      prediction A (sig ω) (e.symm i).1 * S (x i) ω := by
  obtain ⟨⟨β,c⟩, rfl⟩ := e.surjective i
  have h := congrFun (indexedPencilStep_iterate e A S sig Q hQ b x β ω) c
  simpa only [indexedPredictor, hA.1, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
    smul_eq_mul, Equiv.symm_apply_apply] using h

end PencilSearch

end NearSquareRoot
end Computability
end OAI
