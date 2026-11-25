import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteRows

/-! # Extracting the independent transforms from a Hermite work array -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K α L : Type*} [CommSemiring K] [Fintype α] [Fintype L] {W c : ℕ}

/-- At the end of a repair, a row stores one output vector per label.
Reading these vectors together gives the block diagonal over labels and rows. -/
theorem RealizesRows.labelBlocks [DecidableEq L] (A : L → Matrix α α K)
    (h : RealizesRows (fun (x : Fin W → L × α → K) w (p : L × α) =>
      (A p.1).mulVec (fun i => x w (p.1, i)) p.2) c) :
    RealizableAtMost (Matrix.blockDiagonal (fun p : L × Fin W => A p.1)) c := by
  let e : Fin W × (L × α) ≃ α × (L × Fin W) :=
    ⟨fun p => (p.2.2, p.2.1, p.1), fun p => (p.2.2, p.2.1, p.1), fun _ => rfl, fun _ => rfl⟩
  apply (RealizesOp.mulVec_iff _).mp
  convert RealizesOp.reindex h e e using 1
  funext x ⟨o, b⟩
  change (blockDiagonal (fun p : L × Fin W => A p.1)).mulVec x (o, b) =
    (A b.1).mulVec (fun i => x (i, b)) o
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, ite_mul]

/-- Restricting the block outputs to a single label retains all its work rows. -/
theorem RealizesRows.fixedLabelBlocks [DecidableEq L] (A : L → Matrix α α K) (l : L)
    (h : RealizesRows (fun (x : Fin W → L × α → K) w (p : L × α) =>
      (A p.1).mulVec (fun i => x w (p.1, i)) p.2) c) :
    RealizableAtMost (Matrix.blockDiagonal (fun _ : Fin W => A l)) c := by
  let f : α × Fin W ↪ α × (L × Fin W) :=
    ⟨fun p => (p.1, l, p.2), fun _ _ h => congrArg (fun p => (p.1, p.2.2)) h⟩
  convert (h.labelBlocks A).submatrix f f using 1
  ext ⟨i, r⟩ ⟨j, s⟩
  change (if r = s then A l i j else 0) = (if (l, r) = (l, s) then A l i j else 0)
  simp

/-- If all labels request the same matrix, the work array supplies their full
product batch, with the independent inputs numbered consecutively. -/
theorem RealizesRows.uniformLabelBatch (M : Matrix α α K)
    (h : RealizesRows (fun (x : Fin W → L × α → K) w (p : L × α) =>
      M.mulVec (fun i => x w (p.1, i)) p.2) c) :
    RealizableAtMost (Matrix.blockDiagonal (fun _ : Fin (Fintype.card L * W) => M)) c := by
  classical
  let copies := ((Fintype.equivFin L).prodCongr (Equiv.refl (Fin W))).trans finProdFinEquiv
  let e := (Equiv.refl α).prodCongr copies
  convert (h.labelBlocks (fun _ => M)).reindex e e using 1
  ext i j
  simp [e, Matrix.blockDiagonal_apply, Matrix.reindex]

end FiniteFourier
end LinearAlgebra
end OAI
