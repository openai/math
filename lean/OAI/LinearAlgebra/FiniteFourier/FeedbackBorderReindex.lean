import OAI.LinearAlgebra.FiniteFourier.FeedbackReindex

/-! # Changes of coordinates in the geometric feedback model

The pullback of a polynomial equation by a scaled permutation is again polynomial.
Consequently each Zariski-closed feedback bound survives index permutations and
nonzero coordinate scalings.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix MvPolynomial
noncomputable section

variable {K I O I' O' : Type*} [Field K]

private theorem eval_scale_rename {L : Type*} [Field L] (f : O' × I' → O × I)
    (b : O' → L) (a : I' → L) (v : O × I → L) (p : MvPolynomial (O' × I') L) :
    eval v (bind₁ (fun ij => C (b ij.1) * X (f ij) * C (a ij.2)) p) =
      eval (fun ij => b ij.1 * v (f ij) * a ij.2) p := by
  change eval₂Hom (RingHom.id L) v _ = _
  rw [eval₂Hom_bind₁]
  simp only [map_mul, eval₂Hom_C, eval₂Hom_X', RingHom.id_apply]
  rfl

/-- Scaling matrix rows and columns and reindexing them preserves the state bound in closure. -/
theorem GeometricBorderAtMost.scaledReindex {M : Matrix O I K} {s : ℕ}
    (h : GeometricBorderAtMost M s) (eo : O ≃ O') (ei : I ≃ I') (b : O' → K) (a : I' → K) :
    GeometricBorderAtMost (Matrix.of fun o i => b o * M (eo.symm o) (ei.symm i) * a i) s := by
  intro p hp
  let b' : O' → AlgebraicClosure K := fun o => algebraMap K (AlgebraicClosure K) (b o)
  let a' : I' → AlgebraicClosure K := fun i => algebraMap K (AlgebraicClosure K) (a i)
  let f : O' × I' → O × I := fun ij => (eo.symm ij.1, ei.symm ij.2)
  let q := bind₁ (fun ij => C (b' ij.1) * X (f ij) * C (a' ij.2)) p
  have hq (A : Matrix O I (AlgebraicClosure K)) (hA : FeedbackAtMost A s) :
      eval (fun ij => A ij.1 ij.2) q = 0 := by
    dsimp only [q]
    rw [eval_scale_rename]
    exact hp (Matrix.of fun o i => b' o * A (eo.symm o) (ei.symm i) * a' i) (hA.scaledReindex eo ei b' a')
  have he := h q hq
  dsimp only [q] at he
  rw [eval_scale_rename] at he
  simpa only [b', a', f, Matrix.of_apply, map_mul] using he

theorem GeometricBorderAtMost.reindex {M : Matrix O I K} {s : ℕ}
    (h : GeometricBorderAtMost M s) (eo : O ≃ O') (ei : I ≃ I') :
    GeometricBorderAtMost (Matrix.reindex eo ei M) s := by
  have he : Matrix.reindex eo ei M =
      Matrix.of (fun o i => (1 : K) * M (eo.symm o) (ei.symm i) * 1) := by
    ext o i
    simp [Matrix.reindex]
  rw [he]
  exact h.scaledReindex eo ei (fun _ => 1) (fun _ => 1)

theorem GeometricBorderAtMost.smul {M : Matrix O I K} {s : ℕ}
    (h : GeometricBorderAtMost M s) (z : K) : GeometricBorderAtMost (z • M) s := by
  have he : z • M = Matrix.of (fun o i => z * M o i * 1) := by ext; simp
  rw [he]
  exact h.scaledReindex (Equiv.refl _) (Equiv.refl _) (fun _ => z) (fun _ => 1)

/-- Reindexing by bijections preserves geometric border membership in both directions. -/
theorem geometricBorderAtMost_reindex_iff (M : Matrix O I K) (s : ℕ)
    (eo : O ≃ O') (ei : I ≃ I') :
    GeometricBorderAtMost (Matrix.reindex eo ei M) s ↔ GeometricBorderAtMost M s :=
  ⟨fun h => by simpa using h.reindex eo.symm ei.symm, fun h => h.reindex eo ei⟩

/-- Uniform nonzero scaling is free even for geometric border. -/
theorem geometricBorderAtMost_smul_iff (M : Matrix O I K) (s : ℕ)
    {z : K} (hz : z ≠ 0) : GeometricBorderAtMost (z • M) s ↔ GeometricBorderAtMost M s :=
  ⟨fun h => by simpa [smul_smul, hz] using h.smul z⁻¹, fun h => h.smul z⟩

end

end FiniteFourier
end LinearAlgebra
end OAI
