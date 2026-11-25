import OAI.LinearAlgebra.FiniteFourier.PrimeTemplatePass
import OAI.LinearAlgebra.FiniteFourier.CircuitRingCombine
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Free routing and parallel composition of prime-kernel programs -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace PrimeTemplateProgram

variable {K : Type*} [CommSemiring K] {ℓ f F : ℕ} {ζ : K}
variable {I O J P : Type} {c d s t : ℕ}

private theorem wireCircuit (g : O → I) [DecidableEq I] :
    RealizableAtMost ((1 : Matrix I I K).submatrix g id) 0 := by
  refine ⟨0, le_rfl, ⟨.nil, fun o => .scaled 1 (.inl (g o))⟩, ?_⟩
  ext o i
  simp [Circuit.matrix, Circuit.eval, Readout.eval, Matrix.one_apply, Pi.single_apply]

/-- Choose a source register for every output, with free fan-out. -/
theorem route (g : O → I) [DecidableEq I] :
    PrimeTemplateProgram ℓ f F ζ ((1 : Matrix I I K).submatrix g id) 0 0 :=
  .localCircuit (wireCircuit g)

/-- Independent programs run on disjoint banks with additive local work and axis calls. -/
theorem fromBlocks [Fintype I] [Fintype J] [Fintype O] [Fintype P]
    {A : Matrix O I K} {B : Matrix P J K}
    (p : PrimeTemplateProgram ℓ f F ζ A c s) (q : PrimeTemplateProgram ℓ f F ζ B d t) :
    PrimeTemplateProgram ℓ f F ζ (Matrix.fromBlocks A 0 0 B) (c + d) (s + t) := by
  classical
  have h₁ := p.fromBlocks_one P
  have h₂ := (q.fromBlocks_one I).reindex (Equiv.sumComm P I) (Equiv.sumComm J I)
  simpa [Matrix.reindex_apply, Matrix.fromBlocks_multiply] using h₁.serial h₂

private theorem mergeCircuit (O : Type) [Fintype O] [DecidableEq O] :
    RealizableAtMost (Matrix.fromCols (1 : Matrix O O K) (1 : Matrix O O K)) (Fintype.card O) := by
  let read (g : O → O ⊕ O) : Circuit K (O ⊕ O) O 0 := ⟨.nil, fun i => .scaled 1 (.inl (g i))⟩
  obtain ⟨u, hu, q, hq⟩ := circuit_sumPair (O ⊕ O) O (1 : K) 1 (read .inl) (read .inr)
  refine ⟨u, by simpa using hu, q, ?_⟩
  ext o (i | i) <;> unfold Circuit.matrix <;> rw [hq] <;> simp [read, Circuit.eval, Readout.eval,
    Matrix.one_apply, Pi.single_apply]

/-- Run two programs on shared inputs and add their output vectors. -/
theorem add [Fintype I] [Fintype O] {A B : Matrix O I K}
    (p : PrimeTemplateProgram ℓ f F ζ A c s) (q : PrimeTemplateProgram ℓ f F ζ B d t) :
    PrimeTemplateProgram ℓ f F ζ (A + B) (c + d + Fintype.card O) (s + t) := by
  classical
  have dup : PrimeTemplateProgram ℓ f F ζ (Matrix.fromRows (1 : Matrix I I K) (1 : Matrix I I K)) 0 0 := by
    convert route (ℓ := ℓ) (f := f) (F := F) (ζ := ζ) (Sum.elim id id : I ⊕ I → I) using 1
    ext (a | a) b <;> rfl
  have h := (localCircuit (ℓ := ℓ) (f := f) (F := F) (ζ := ζ) (mergeCircuit O)).serial
    ((p.fromBlocks q).serial dup)
  simpa [Matrix.fromBlocks_mul_fromRows, Matrix.fromCols_mul_fromRows, Nat.add_comm] using h

/-- Sum a finite family, allowing one addition per output for each summand. -/
theorem sum_finset {L : Type*} [Fintype I] [Fintype O] (u : Finset L)
    {A : L → Matrix O I K} {c s : L → ℕ}
    (p : ∀ l ∈ u, PrimeTemplateProgram ℓ f F ζ (A l) (c l) (s l)) :
    PrimeTemplateProgram ℓ f F ζ (∑ l ∈ u, A l)
      (∑ l ∈ u, (c l + Fintype.card O)) (∑ l ∈ u, s l) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact localCircuit ⟨0, le_rfl, ⟨.nil, fun _ => .zero⟩, by ext; rfl⟩
  | @insert l u hl ih =>
    rw [Finset.sum_insert hl, Finset.sum_insert hl, Finset.sum_insert hl]
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (p l (Finset.mem_insert_self ..)).add (ih (fun j hj => p j (Finset.mem_insert_of_mem hj)))

end PrimeTemplateProgram

end FiniteFourier
end LinearAlgebra
end OAI
