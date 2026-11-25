import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteRows
import OAI.LinearAlgebra.FiniteFourier.PrimeTemplate

/-! # The routed pencil in Hermite row coordinates

The constant term mixes only clock rows. Adding the weighted query terms
gives the ordinary pencil stage on the work space whose coordinate is a
label together with a digit array.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open scoped Classical
open Matrix

variable {K : Type*} [CommSemiring K]
variable {L W X A J : Type}

/-- At every label and every digit array entry, apply the same clock-row matrix. -/
def routedConstantMatrix (B : Matrix W W K) : Matrix ((L × W) × X) ((L × W) × X) K :=
  of fun o i => if o.1.1 = i.1.1 then (if o.2 = i.2 then B o.1.2 i.1.2 else 0) else 0

/-- The constant coefficient of a pencil requires no Fourier calls. -/
theorem routedConstant_template [Fintype L] [Fintype W] [Fintype X] {ℓ f F : ℕ} {ζ : K}
    (B : Matrix W W K) :
    PrimeTemplateProgram ℓ f F ζ (routedConstantMatrix (L := L) (X := X) B)
      (Fintype.card L * Fintype.card W ^ 2 * Fintype.card X) 0 := by
  let e := (Equiv.prodAssoc W L X).symm.trans
    ((Equiv.prodComm W L).prodCongr (Equiv.refl X))
  apply PrimeTemplateProgram.localCircuit
  convert ((realizableAtMost_card_mul_card B).blockDiagonal (L × X)).reindex e e using 1
  · ext ⟨⟨l,w⟩,x⟩ ⟨⟨l',w'⟩,x'⟩
    simp [routedConstantMatrix, e, Matrix.reindex_apply, Matrix.blockDiagonal_apply, ite_and]
  · rw [Fintype.card_prod]
    ring

/-- The full routed pencil. The rectangle corrections cancel all terms
linking distinct labels. -/
def routedPencilMatrix [Fintype A] [Fintype J] (B₀ : Matrix W W K)
    (B : A → J → Matrix W W K) (Q : A → J → Matrix X X K) :
    Matrix ((L × W) × X) ((L × W) × X) K :=
  of fun o i => if o.1.1 = i.1.1 then
    (if o.2 = i.2 then B₀ o.1.2 i.1.2 else 0) +
      ∑ a, ∑ j, B a j o.1.2 i.1.2 * Q a j o.2 i.2 else 0

/-- Exchange the label and work-row indices to obtain the row convention
used in the Hermite repair. -/
def routedRowEquiv (L W X : Type) : (L × W) × X ≃ W × (L × X) :=
  ((Equiv.prodComm L W).prodCongr (Equiv.refl X)).trans (Equiv.prodAssoc W L X)

variable [Fintype L] [Fintype W] [Fintype X] [Fintype A] [Fintype J]

/-- The matrix of a completed pencil first mixes the rows for each
coefficient and then applies its query on the array at the given label. -/
theorem routedPencilMatrix_mulVec (B₀ : Matrix W W K) (B : A → J → Matrix W W K)
    (Q : A → J → Matrix X X K) (v : W × (L × X) → K) (w : W) (l : L) (x : X) :
    (Matrix.reindex (routedRowEquiv L W X) (routedRowEquiv L W X)
      (routedPencilMatrix B₀ B Q)).mulVec v (w,l,x) =
    (B₀ *ᵥ fun i => v (i,l,x)) w +
      ∑ a, ∑ j, (Q a j *ᵥ (fun y => (B a j *ᵥ fun i => v (i,l,y)) w)) x := by
  have hEntry (w' : W) (l' : L) (y : X) :
      Matrix.reindex (routedRowEquiv L W X) (routedRowEquiv L W X)
        (routedPencilMatrix B₀ B Q) (w,l,x) (w',l',y) =
      if l = l' then (if x = y then B₀ w w' else 0) +
        ∑ a, ∑ j, B a j w w' * Q a j x y else 0 := rfl
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, hEntry, ite_mul, Finset.sum_ite_irrel,
    add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm]
    arg 2; ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Reindexing the completed transfer gives a realization on Hermite work
rows with exactly the same gate budget. -/
theorem realizesRows_routedPencilMatrix (B₀ : Matrix W W K) (B : A → J → Matrix W W K)
    (Q : A → J → Matrix X X K) {n : ℕ}
    (hc : RealizableAtMost (routedPencilMatrix (L := L) B₀ B Q) n) :
    RealizesRows (fun (v : W → L × X → K) w p =>
      (B₀ *ᵥ fun i => v i p) w +
        ∑ a, ∑ j, (Q a j *ᵥ fun y => (B a j *ᵥ fun i => v i (p.1,y)) w) p.2) n := by
  refine ⟨_, hc.reindex (routedRowEquiv L W X) (routedRowEquiv L W X), fun v => ?_⟩
  funext ⟨w,l,x⟩
  exact routedPencilMatrix_mulVec B₀ B Q v w l x

end

end

end FiniteFourier
end LinearAlgebra
end OAI
