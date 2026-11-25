import OAI.LinearAlgebra.FiniteFourier.PrimeTemplateReindex

/-! # Preserved registers for a complete prime Fourier template -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K : Type*} [CommSemiring K] {ℓ f F c s : ℕ} {ζ : K}
variable {I O : Type} {M : Matrix O I K}

/-- Keep an auxiliary register bank intact throughout a complete template. The auxiliary
wires are available at every oracle call, at the same gate and call budgets. -/
theorem PrimeTemplateProgram.fromBlocks_one [finI : Fintype I] (p : PrimeTemplateProgram ℓ f F ζ M c s)
    (T : Type) [Fintype T] [DecidableEq T] :
    PrimeTemplateProgram ℓ f F ζ (Matrix.fromBlocks M 0 0 (1 : Matrix T T K)) c s := by
  classical
  revert finI
  induction p with
  | localCircuit hp =>
    intro _
    have hpass : RealizableAtMost (1 : Matrix T T K) 0 := by
      refine ⟨0, le_rfl, ⟨.nil, fun i => .scaled 1 (.inl i)⟩, ?_⟩
      ext i j
      simp [Circuit.matrix, Circuit.eval, Readout.eval, Matrix.one_apply, Pi.single_apply]
    exact .localCircuit (by simpa using hp.fromBlocks hpass)
  | axis S =>
    intro _
    let e := (Equiv.sumAssoc ((Fin f → Fin ℓ) × Fin F) S T).symm
    have h := (PrimeTemplateProgram.axis (ℓ := ℓ) (f := f) (F := F) (ζ := ζ) (S ⊕ T)).reindex e e
    convert h using 1
    ext o i
    rcases o with (a | b) | c <;> rcases i with (j | k) | l <;>
      simp [e, Matrix.reindex_apply, Matrix.fromBlocks, Matrix.one_apply]
  | serial hM hN ihM ihN =>
    intro _
    simpa [Matrix.fromBlocks_multiply] using (ihM.serial ihN)

end FiniteFourier
end LinearAlgebra
end OAI
