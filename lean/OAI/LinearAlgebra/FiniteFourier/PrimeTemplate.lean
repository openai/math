import OAI.LinearAlgebra.FiniteFourier.PrimeKernel

/-! # Compilation of a prime-kernel template

The oracle used by the repair and routing construction is an ordinary circuit
on one `f`-digit axis of a work row. Other live coordinates pass through the
call. This file keeps the local gate count and the number of axis calls
separate until the template is instantiated.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K : Type*} [CommSemiring K]

/-- A program with local linear circuits, single-axis Fourier calls,
and serial composition. Each call to an f-digit axis transforms all F fibers
of one work row and preserves an arbitrary finite bank of other registers. -/
inductive PrimeTemplateProgram (ℓ f F : ℕ) (ζ : K) :
    {I O : Type} → Matrix O I K → ℕ → ℕ → Prop where
  | localCircuit {I O : Type} {M : Matrix O I K} {c : ℕ} (h : RealizableAtMost M c) :
      PrimeTemplateProgram ℓ f F ζ M c 0
  | axis (T : Type) [Fintype T] [DecidableEq T] :
      PrimeTemplateProgram ℓ f F ζ (Matrix.fromBlocks
        (Matrix.blockDiagonal fun _ : Fin F => primeTransform ℓ f ζ) 0 0 (1 : Matrix T T K)) 0 1
  | serial {I J O : Type} [Fintype J] {M : Matrix O J K} {N : Matrix J I K}
      {c d s t : ℕ} (hM : PrimeTemplateProgram ℓ f F ζ M c s)
      (hN : PrimeTemplateProgram ℓ f F ζ N d t) :
      PrimeTemplateProgram ℓ f F ζ (M * N) (c + d) (s + t)

/-- Substitute an actual f-digit Fourier circuit in every axis call. -/
theorem PrimeTemplateProgram.compile {ℓ f F : ℕ} {ζ : K} {I O : Type} {M : Matrix O I K}
    {c s : ℕ} (p : PrimeTemplateProgram ℓ f F ζ M c s) :
    RealizableAtMost M (c + s * F * complexity (primeTransform ℓ f ζ)) := by
  induction p with
  | localCircuit hp => simpa using hp
  | axis T =>
    classical
    have haxis := (realizableAtMost_complexity (primeTransform ℓ f ζ)).blockDiagonal (Fin F)
    have hpass : RealizableAtMost (1 : Matrix T T K) 0 := by
      refine ⟨0, le_rfl, ⟨.nil, fun i => .scaled 1 (.inl i)⟩, ?_⟩
      ext i j
      simp [Circuit.matrix, Circuit.eval, Readout.eval, Matrix.one_apply, Pi.single_apply]
    simpa using haxis.fromBlocks hpass
  | serial _ _ ihM ihN =>
    convert ihM.mul ihN using 1
    ring

/-- A template with at most σ axis calls and linear local work gives the
finite batch inequality. Its row width, arity, and call budget are fixed
across the digit lengths f. -/
theorem primeKernelBatch_of_template {ℓ A W σ C : ℕ} {ζ : K}
    (h : ∀ f : ℕ, 0 < f → ∃ c ≤ C * ℓ ^ (A*f), ∃ s ≤ σ,
      PrimeTemplateProgram ℓ f (ℓ^((A-1)*f)) ζ
        (Matrix.blockDiagonal fun _ : Fin W => primeTransform ℓ (A*f) ζ) c s) :
    PrimeKernelBatch ℓ A W σ C ζ := by
  intro f hf
  obtain ⟨c, hc, s, hs, hp⟩ := h f hf
  obtain ⟨r, hr, q, hq⟩ := hp.compile
  exact ⟨r, hr.trans (Nat.add_le_add hc (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hs))), q, hq⟩

end FiniteFourier
end LinearAlgebra
end OAI
