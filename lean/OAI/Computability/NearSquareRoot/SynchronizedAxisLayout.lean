import OAI.Computability.NearSquareRoot.SynchronizedAxisProduct

/-! # Relocating each physical batch to explicit spectator-fiber numbers -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open Matrix Finset SynchronizedPadding ResidueFourier

noncomputable section

variable {m : ℕ} (a c : Fin m → ℕ) [∀ i, NeZero (a i)]

/-- The physical address of a chosen axis and the number assigned to its spectator tuple. -/
def axisLayout (spectator : ∀ j, Spectators a c j ≃ Fin (Fintype.card (Spectators a c j)))
    (j : Fin m) :
    (∀ i, BlockAxis a c i) ≃ Fin (Fintype.card (Spectators a c j)) × (Fin (a j) ⊕ Fin (c j)) :=
  (Equiv.piSplitAt j _).trans ((Equiv.prodComm ..).trans
    ((spectator j).prodCongr ((ZMod.finEquiv (a j)).symm.sumCongr (Equiv.refl _))))

variable (spectator : ∀ j, Spectators a c j ≃ Fin (Fintype.card (Spectators a c j)))

private theorem axisPass_eq (j : Fin m) :
    (fiberMatrix (c := c j) (Fintype.card (Spectators a c j)) (normalizedFourier (a j))).submatrix
      (axisLayout a c spectator j) (axisLayout a c spectator j) =
    tensorMatrix (atAxis (fun i => axisPadding (b := Fin (c i)) (axisMatrix (a i))) j) := by
  ext x y
  rw [atAxis_apply]
  simp only [fiberMatrix, Matrix.submatrix_apply, Prod.swap, blockDiagonal_apply, axisLayout,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodComm_apply, Equiv.piSplitAt_apply,
    Prod.map_apply, Equiv.apply_eq_iff_eq]
  exact congrArg (fun z : ℂ => if (fun s : {i // i ≠ j} => x s.val) =
    (fun s : {i // i ≠ j} => y s.val) then z else 0) (padded_eq a c j (x j) (y j))

/-- The product of all axis passes in their actual tape order computes the block transform. -/
theorem axisPass_prod :
    ((List.finRange m).map (fun j =>
      (fiberMatrix (c := c j) (Fintype.card (Spectators a c j)) (normalizedFourier (a j))).submatrix
        (axisLayout a c spectator j) (axisLayout a c spectator j))).prod =
    tensorMatrix (fun i => axisPadding (b := Fin (c i)) (axisMatrix (a i))) := by
  let U := fun i : Fin m => axisPadding (b := Fin (c i)) (axisMatrix (a i))
  have H (l : List (Fin m)) (hn : l.Nodup) : (l.map (fun j => tensorMatrix (atAxis U j))).prod =
      tensorMatrix (fun i => if i ∈ l then U i else 1) := by
    induction l with
    | nil => simp
    | cons j l ih =>
      obtain ⟨hj,hl⟩ := List.nodup_cons.mp hn
      rw [List.map_cons, List.prod_cons, ih hl, ← tensorMatrix_mul]
      congr 1
      funext i
      by_cases hij : i = j
      · subst i; simp [atAxis, hj]
      · simp [atAxis, hij]
  simp_rw [axisPass_eq]
  simpa [U] using H (List.finRange m) (List.nodup_finRange _)

end
end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
