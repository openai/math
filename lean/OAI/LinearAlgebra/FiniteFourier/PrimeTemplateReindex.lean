import OAI.LinearAlgebra.FiniteFourier.PrimeTemplate

/-! # Wiring prime Fourier templates -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K : Type*} [CommSemiring K] {ℓ f F c s : ℕ} {ζ : K}
variable {I O I' O' : Type} {M : Matrix O I K}

private theorem diagonal_free {J : Type} [DecidableEq J] (a : J → K) :
    RealizableAtMost (Matrix.diagonal a) 0 := by
  refine ⟨0, le_rfl, ⟨.nil, fun i => .scaled (a i) (.inl i)⟩, ?_⟩
  ext i j
  by_cases h : i = j <;> simp [Circuit.matrix, Circuit.eval, Readout.eval, h]

private theorem one_free (J : Type) [DecidableEq J] : RealizableAtMost (1 : Matrix J J K) 0 := by
  simpa using diagonal_free (fun _ : J => (1 : K))

/-- Select output rows and set omitted input coordinates to zero using only wiring. -/
theorem PrimeTemplateProgram.submatrix [Fintype O] [Fintype I]
    (p : PrimeTemplateProgram ℓ f F ζ M c s) (g : O' → O) (h : I' ↪ I) :
    PrimeTemplateProgram ℓ f F ζ (M.submatrix g h) c s := by
  classical
  have hl := (one_free (K := K) O).submatrix g (Function.Embedding.refl O)
  have hr := (one_free (K := K) I).submatrix id h
  have hprod := ((PrimeTemplateProgram.localCircuit hl).serial p).serial (.localCircuit hr)
  change PrimeTemplateProgram ℓ f F ζ
    (((1 : Matrix O O K).submatrix g (Equiv.refl O)) * M *
      (1 : Matrix I I K).submatrix (Equiv.refl I) h) _ _ at hprod
  rw [Matrix.one_submatrix_mul, Matrix.mul_submatrix_one] at hprod
  simpa [Matrix.submatrix_submatrix] using hprod

/-- Relabel the external wires of a template at its original gate and call budgets. -/
theorem PrimeTemplateProgram.reindex [Fintype O] [Fintype I]
    (p : PrimeTemplateProgram ℓ f F ζ M c s) (eo : O ≃ O') (ei : I ≃ I') :
    PrimeTemplateProgram ℓ f F ζ (Matrix.reindex eo ei M) c s :=
  p.submatrix eo.symm ei.symm.toEmbedding

/-- Apply free diagonal scalings to the input and output wires of a complete template. -/
theorem PrimeTemplateProgram.diagonal [Fintype O] [Fintype I]
    (p : PrimeTemplateProgram ℓ f F ζ M c s) (b : O → K) (a : I → K) :
    PrimeTemplateProgram ℓ f F ζ (Matrix.of fun o i => b o * (a i * M o i)) c s := by
  classical
  have q := ((PrimeTemplateProgram.localCircuit (diagonal_free b)).serial p).serial
    (.localCircuit (diagonal_free a))
  have he : Matrix.diagonal b * M * Matrix.diagonal a =
      Matrix.of (fun o i => b o * (a i * M o i)) := by
    ext o i
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_assoc, mul_comm (a i)]
  simpa [he] using q

/-- A single oracle call on a bank indexed by any finite set of the prescribed cardinality. -/
theorem PrimeTemplateProgram.axis_blockDiagonal (T : Type) [Fintype T] [DecidableEq T]
    (hT : Fintype.card T = F) :
    PrimeTemplateProgram ℓ f F ζ (Matrix.blockDiagonal fun _ : T => primeTransform ℓ f ζ) 0 1 := by
  classical
  let e := (Fintype.equivFinOfCardEq hT).symm
  let g := (Equiv.sumEmpty ((Fin f → Fin ℓ) × Fin F) Empty).trans
    (Equiv.prodCongr (Equiv.refl (Fin f → Fin ℓ)) e)
  have p := (PrimeTemplateProgram.axis (ℓ := ℓ) (f := f) (F := F) (ζ := ζ) Empty).reindex g g
  convert p using 1
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [g, Matrix.reindex_apply, Matrix.blockDiagonal_apply, Equiv.sumEmpty]

end FiniteFourier
end LinearAlgebra
end OAI
