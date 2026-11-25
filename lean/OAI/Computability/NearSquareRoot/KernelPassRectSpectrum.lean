import OAI.Computability.NearSquareRoot.KernelPassRectPencil
import OAI.Computability.NearSquareRoot.KernelPassFrequency

/-! # Frequency action of a label-diagonal row pencil

A zero-call reindexing puts each label's internal rows in the numbering
of the Hermite stage. At every frequency the pencil acts independently
on these banks with the indicated query eigenvalues.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect
open Matrix Finset
open scoped BigOperators

variable {A h n : ℕ} {L W J I O : Type} [Fintype L] [Fintype W] [Fintype J] [Fintype I] [Fintype O]

/-- Change from the chosen finite numbering to a supplied row layout. -/
noncomputable def renumber (e : I ≃ Fin n) (p : On A I I) : Plan A n n :=
  (Plan.route ((Fintype.equivFin I) ∘ e.symm)).seq
    (p.seq (Plan.route (e ∘ (Fintype.equivFin I).symm)))

@[simp] theorem calls_renumber (e : I ≃ Fin n) (p : On A I I) :
    (renumber e p).calls = p.calls := by simp [renumber, Plan.calls]

theorem row_action (p : On A I O) (x : Bank A h (Fintype.card I)) (b : O) :
    p.applyAt h x (Fintype.equivFin O b) =
      ∑ a : I, block (I := I) (O := O) p h b a *ᵥ x (Fintype.equivFin I a) := by
  funext y
  simp only [Plan.applyAt, Function.curry_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Function.uncurry, Finset.sum_apply, block]
  exact ((Fintype.equivFin I).sum_comp _).symm

theorem renumber_action (e : I ≃ Fin n) (p : On A I I) (x : Bank A h n) (b : I) :
    (renumber e p).applyAt h x (e b) = ∑ a : I, block (I := I) (O := I) p h b a *ᵥ x (e a) := by
  rw [renumber, Plan.applyAt_seq, Plan.applyAt_route, Plan.applyAt_seq, Plan.applyAt_route]
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [row_action (I := I) (O := I)]
  simp

variable [DecidableEq L]

/-- A label-diagonal pencil applied to one independent input stream bank. -/
theorem atFrequency (e : L × W ≃ Fin n) (p : On A (L × W) (L × W))
    (B₀ : W → W → ℚ) (B : J → W → W → ℚ) (H : J → L → Mat A h)
    (s : J → L → Addr A h → ℚ)
    (hp : ∀ (w v : L) (k l : W), block (I := L × W) (O := L × W) p h (w,k) (v,l) =
      if w = v then B₀ k l • (1 : Mat A h) + ∑ j, B j k l • H j w else 0)
    (hs : ∀ j w (v : Addr A h → ℚ) y,
      (Plan.walshMatrix A h *ᵥ (H j w *ᵥ v)) y = s j w y * (Plan.walshMatrix A h *ᵥ v) y)
    (x : Bank A h n) (w : L) (k : W) (y : Addr A h) :
    Plan.frequency ((renumber e p).applyAt h x) (e (w,k)) y =
      ∑ l, (B₀ k l + ∑ j, (s j w y) * B j k l) * Plan.frequency x (e (w,l)) y := by
  classical
  change (Plan.walshMatrix A h *ᵥ ((renumber e p).applyAt h x (e (w,k)))) y = _
  rw [renumber_action, Fintype.sum_prod_type]
  have ite_vec (P : Prop) [Decidable P] (M : Mat A h) (v : Addr A h → ℚ) :
      (if P then M else 0) *ᵥ v = if P then M *ᵥ v else 0 := by split <;> simp
  simp only [hp, ite_vec]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, Matrix.mulVec_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sum, Pi.add_apply, Pi.smul_apply,
    Finset.sum_apply, hs, smul_eq_mul, add_mul, Finset.sum_mul, Plan.frequency]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

end KernelPass.Rect

end NearSquareRoot
end Computability
end OAI
