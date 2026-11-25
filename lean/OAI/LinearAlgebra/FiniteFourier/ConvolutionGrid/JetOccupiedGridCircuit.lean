import OAI.LinearAlgebra.FiniteFourier.FiberSynchronization
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridProduct
import OAI.LinearAlgebra.FiniteFourier.AtTwoJetMatrixReindex
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyMonomial

/-! # Compiling a family of occupied axis words in jet coordinates

The axes may have different input and output labels. Their square occupied
words synchronize after relabeling, using one common workspace whose size
is proportional to the entire grid. Rewiring the compiled circuit recovers
exactly the input and output labels of the tensor of the rectangular matrices.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid

open Polynomial Matrix

/-- Base-ring cost of a synchronized tensor with space ratio `c` and local depth `d`. -/
noncomputable def occupiedGridJetCost (β C : ℝ) (c d N e h s : ℕ) : ℝ :=
  let D := fiberDepthFactor c * d
  let V : ℝ := c*N
  D * (V*(40*e*h*convolutionEnvelope s) + (2*e*h)*(C*V*(1+Real.logb 2 V)^β))

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {η : S} {m : S[X]}
  {σ : Type} [Fintype σ] [DecidableEq σ] {I O X W : σ → Type}
  [∀ i, Fintype (I i)] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)] {c d e h s : ℕ} {β C : ℝ}

/-- Compile the tensor of all axis words on base-ring coordinates. -/
theorem occupiedGridMatrixCircuit (A : ∀ i, Matrix (O i) (I i) (JetQuotient m h))
    (out : ∀ i, X i ≃ O i) (inp : ∀ i, X i ≃ I i) (hc : 0 < c)
    (ha : ∀ i, 2 ≤ Fintype.card (X i)) (hw : ∀ i, Fintype.card (W i) ≤ Fintype.card (X i)*(c-1))
    (words : ∀ i, OccupiedWord (W i) d ((A i).submatrix (out i) (inp i)))
    (jets : JetCircuitsOver (algebraMap R S) η m e h)
    (hb : Function.Bijective (fun t : Fin 2 → R => algebraMap R S (t 0) + η*algebraMap R S (t 1)))
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e) (hh : 0 < h) (hs : 2*e*h ≤ s)
    (ht : ShearTensorBound R β C) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    JetMatrixCircuit (algebraMap R S) η m e h (columns A)
      (occupiedGridJetCost β C c d (Fintype.card (∀ i, X i)) e h s) := by
  classical
  have H := occupiedWord_gridTensor hc ha hw words
  have q := (H.jetMatrixCircuit jets hb hm hd he hh hs ht hβ hC).eliminateWorkspace
  have hV (N : ℕ) : Fintype.card ((∀ i, X i) ⊕ Fin (N*(c-1))) =
      Fintype.card (∀ i, X i) + N*(c-1) := by simp
  have hcN (N : ℕ) : N+N*(c-1) = c*N := by
    obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
    rw [Nat.succ_sub_one, Nat.succ_mul]
    ring
  simp only [hV, hcN, Nat.cast_mul] at q
  have Q := q.reindex (Equiv.piCongrRight out).symm (Equiv.piCongrRight inp).symm
  convert Q using 2
  · ext a b
    simp [gridTensor, columns]
  · simp [occupiedGridJetCost]

end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
