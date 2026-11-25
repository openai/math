import OAI.Computability.NearSquareRoot.SynchronizedFiberWord
import OAI.Computability.NearSquareRoot.SynchronizedLayerTensor
import OAI.Computability.NearSquareRoot.SynchronizedCirculant

/-! Successive transforms of the individual axes of one small block. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix Finset SynchronizedPadding ResidueFourier

noncomputable section

variable {m : ℕ} {A : Fin m → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- The single nonidentity factor in an axis pass. -/
def atAxis (U : ∀ i, Matrix (A i) (A i) ℂ) (j : Fin m) : ∀ i, Matrix (A i) (A i) ℂ :=
  Function.update 1 j (U j)

omit [∀ i, Fintype (A i)] in
theorem atAxis_apply (U : ∀ i, Matrix (A i) (A i) ℂ) (j : Fin m)
    (x y : ∀ i, A i) :
    tensorMatrix (atAxis U j) x y =
      if (fun k : {i // i ≠ j} ↦ x k.val) = (fun k : {i // i ≠ j} ↦ y k.val)
      then U j (x j) (y j) else 0 := by
  classical
  change (∏ i : Fin m, (atAxis U j i) (x i) (y i)) = _
  split_ifs with ho
  · rw [prod_eq_single j]
    · simp [atAxis]
    · intro i _ hij
      have hxy := congrFun ho ⟨i,hij⟩
      simpa [atAxis, Function.update_of_ne hij, Matrix.one_apply] using hxy
    · simp
  · obtain ⟨⟨i,hij⟩,hi⟩ := Function.ne_iff.mp ho
    apply prod_eq_zero (mem_univ i)
    simp [atAxis, Function.update_of_ne hij, hi]

private theorem tensorAxisWords (U : ∀ i, Matrix (A i) (A i) ℂ) (d : ℕ)
    (h : ∀ j, HasShortWord (tensorMatrix (atAxis U j)) d) :
    HasShortWord (tensorMatrix U) (m * d) := by
  classical
  let F (l : List (Fin m)) := fun i ↦ if i ∈ l then U i else 1
  have H (l : List (Fin m)) (hn : l.Nodup) :
      HasShortWord (tensorMatrix (F l)) (l.length * d) := by
    induction l with
    | nil =>
      simpa [F] using (HasShortWord.empty (A := ∀ i, A i))
    | cons j l ih =>
      obtain ⟨hj,hl⟩ := List.nodup_cons.mp hn
      have mul : tensorMatrix (F (j::l)) = tensorMatrix (atAxis U j) * tensorMatrix (F l) := by
        rw [← tensorMatrix_mul]
        congr 1
        funext i
        by_cases hij : i = j
        · subst i; simp [F, atAxis, hj]
        · simp [F, atAxis, hij]
      rw [mul]
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      rw [Nat.add_comm]
      exact (h j).append (ih hl)
  simpa [F] using H (List.finRange m) (List.nodup_finRange _)

variable (a c : Fin m → ℕ) [∀ i, NeZero (a i)]

abbrev BlockAxis (j : Fin m) := ZMod (a j) ⊕ Fin (c j)
abbrev Spectators (j : Fin m) := ∀ s : {i // i ≠ j}, BlockAxis a c s.val

/-- The spectator-fiber number, followed by the active or spare part of one axis. -/
private def layout (j : Fin m) :
    (∀ i, BlockAxis a c i) ≃ Fin (Fintype.card (Spectators a c j)) × (Fin (a j) ⊕ Fin (c j)) :=
  (Equiv.piSplitAt j _).trans ((Equiv.prodComm ..).trans
    ((Fintype.equivFin (Spectators a c j)).prodCongr
      ((ZMod.finEquiv (a j)).symm.sumCongr (Equiv.refl _))))

theorem padded_eq (j : Fin m) (x y : BlockAxis a c j) :
    let f := (ZMod.finEquiv (a j)).symm.sumCongr (Equiv.refl (Fin (c j)))
    axisPadding (normalizedFourier (a j)) (f x) (f y) = axisPadding (axisMatrix (a j)) x y := by
  cases x <;> cases y <;> simp [axisPadding, normalizedFourier_axisMatrix, submatrix_apply]

private theorem axisWord {D : ℕ} (j : Fin m)
    (h : HasShortWord (fiberMatrix (c := c j) (Fintype.card (Spectators a c j)) (normalizedFourier (a j))) D) :
    HasShortWord (tensorMatrix (atAxis (fun i ↦ axisPadding (b := Fin (c i)) (axisMatrix (a i))) j)) D := by
  let e := layout a c j
  have eq : (fiberMatrix (c := c j) (Fintype.card (Spectators a c j)) (normalizedFourier (a j))).submatrix e e =
      tensorMatrix (atAxis (fun i ↦ axisPadding (b := Fin (c i)) (axisMatrix (a i))) j) := by
    ext x y
    rw [atAxis_apply]
    simp only [fiberMatrix, Matrix.submatrix_apply, Prod.swap, blockDiagonal_apply, e, layout,
      Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodComm_apply, Equiv.piSplitAt_apply,
      Prod.map_apply, Equiv.apply_eq_iff_eq]
    exact congrArg (fun z : ℂ ↦ if (fun s : {i // i ≠ j} ↦ x s.val) =
      (fun s : {i // i ≠ j} ↦ y s.val) then z else 0) (padded_eq a c j (x j) (y j))
  rw [← eq]
  exact h.relocate e.symm

/-- If each individual fiber pass has depth at most `D`, executing all of them
on the same addresses gives the exact tensor transform of depth at most `m*D`. -/
theorem blockTensor_word {D : ℕ}
    (h : ∀ j, HasShortWord (fiberMatrix (c := c j) (Fintype.card (Spectators a c j))
      (normalizedFourier (a j))) D) :
    HasShortWord (tensorMatrix fun i ↦ axisPadding (b := Fin (c i)) (axisMatrix (a i))) (m*D) :=
  tensorAxisWords _ D fun j ↦ axisWord a c j (h j)

end
end ShortFourier

end NearSquareRoot
end Computability
end OAI
