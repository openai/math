import OAI.LinearAlgebra.SpectralBooks.CopyLabelTensor
import OAI.LinearAlgebra.SpectralBooks.CopyLabelContraction
import OAI.LinearAlgebra.SpectralBooks.DiagonalRestriction

/-! # Degeneration for copying a label shared by two sites

The common-label specialization with two original recipients and one new
recipient acts on an arbitrary tensor carrying that same label at the two
original recipients. Each coefficient of the old tensor multiplies the
corresponding auxiliary coordinate throughout the degeneration.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw
noncomputable section
open scoped Classical

variable {I : Type} [Fintype I] {K : Type*} [Field K] [Infinite K]

/-- The copied tensor times a returned independent wire occurs in the
fixed-format Zariski closure of restrictions from the original tensor times
a diagonal of dimension `4 * (q - 1) + 1`. -/
theorem copyOutput_mem_closure {q : ℕ} (T : Raw.{0} I K) (σ : Fin 3 → I)
    (hA : T.Leg (σ 0) → Fin q) (hB : T.Leg (σ 1) → Fin q)
    (hmatch : ∀ x, T.coeff x ≠ 0 → hA (x (σ 0)) = hB (x (σ 1))) :
    (T.copyOutput σ hA).coeff ∈ affineZariskiClosure
      {S | Crossing.IsRestriction S
        (T.mul ((diagonal (Fin 3) K (Fin (4 * (q - 1) + 1))).group σ)).coeff} := by
  let Y := T.copyOutput σ hA
  let old (y : ∀ i, Y.Leg i) (i : I) := (y i).1
  let aux (y : ∀ i, Y.Leg i) (r : Fin 3) := (y (σ r)).2 ⟨r, rfl⟩
  let read (y : ∀ i, Y.Leg i) : IncrementCoordinate q 1 0 :=
    ⟨hA (old y (σ 0)), aux y 0, aux y 2, fun _ => hB (old y (σ 1)),
      fun _ => aux y 1, Fin.elim0⟩
  let pol (y : ∀ i, Y.Leg i) : MvPolynomial (IncrementCoordinate q 1 0) K :=
    MvPolynomial.C (T.coeff (old y)) * MvPolynomial.X (read y)
  have eval (Z : IncrementCoordinate q 1 0 → K) (y : ∀ i, Y.Leg i) :
      MvPolynomial.eval Z (pol y) = T.coeff (old y) * Z (read y) := by simp [pol]
  have shared (y : ∀ i, Y.Leg i) (hy : T.coeff (old y) ≠ 0) : (read y).shared := by
    exact ⟨fun _ => (hmatch (old y) hy).symm, fun j => j.elim0⟩
  have target : (T.copyOutput σ hA).coeff =
      fun y => MvPolynomial.eval (commonLabelTarget K) (pol y) := by
    funext y
    rw [eval]
    change T.coeff (old y) * (if aux y 0 = aux y 1 ∧ aux y 2 = hA (old y (σ 0)) then 1 else 0) =
      T.coeff (old y) * _
    by_cases hy : T.coeff (old y) = 0
    · simp [hy]
    · simp [commonLabelTarget, shared y hy, read, (eq_comm (a := aux y 0) (b := aux y 1)), and_comm]
  rw [target]
  apply mapsTo_affineZariskiClosure_of_polynomial pol _
    (commonLabelTarget_mem_closure K q 1 0)
  rintro Z ⟨U, V, G, hZ⟩
  let L := 4 * (q - 1) + 1
  let M : (r : Fin 3) → T.Leg (σ r) → Fin q → Fin L → K := Fin.cons
    (fun t a l => U (hA t) a l) (Fin.cons (fun t b l => V 0 (hB t) b l)
      (Fin.cons (fun _ g l => G g l) (fun j => j.elim0)))
  have h := restrict_controlled_diagonal σ T (fun _ => Fin q) L M
  change Crossing.IsRestriction _ _
  suffices hcoeff : (fun y => MvPolynomial.eval Z (pol y)) =
      (controlledDiagonal σ T (fun _ => Fin q) L M).coeff by
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun y => (congrFun hcoeff y).trans (hN y)⟩
  funext y
  rw [eval, hZ]
  by_cases hy : T.coeff (old y) = 0
  · change T.coeff (old y) * _ = T.coeff (old y) * _
    simp [hy]
  · simp only [shared y hy, ↓reduceIte]
    apply congrArg (T.coeff (old y) * ·)
    apply Finset.sum_congr rfl
    intro l _
    simp [Fin.prod_univ_succ, M, read, old, aux, mul_assoc]

end
end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
