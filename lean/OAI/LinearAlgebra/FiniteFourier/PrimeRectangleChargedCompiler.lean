import OAI.LinearAlgebra.FiniteFourier.PrimeCommonCost
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonCostRouting
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleTransfer
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleCharged
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedPieces
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedUniform

/-! # Charged rectangles of the ordinary prime pencil

All incident labels express the transfer in coordinates of a single paired
space. The source and destination charts are free wire permutations around
one common transform per clock row.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
namespace BitRoutingGeometry
open scoped Classical

variable {ℓ L b : ℕ} [Fact ℓ.Prime] (G : BitRoutingGeometry ℓ L b)
variable {K : Type*} [CommRing K] [Invertible (ℓ : K)] {ζ : K}

/-- Compute the physical common transform on the spectator fibers of a query. -/
theorem queryCommon_template (hζ : IsPrimitiveRoot ζ ℓ) {m : ℕ} (f : ℕ)
    (a : (ZMod ℓ)ˣ) (j : Fin m) :
    PrimeTemplateProgram ℓ f (G.axisFibers m f) ζ
      (primeCommonKernel (C := Fin f) (T := PrimeCommonSpectators (Fin f) j ℓ) hζ G.form a G.D)
      0 (2 * G.D) := by
  classical
  let e := Pi.basisFun (ZMod ℓ) (Fin G.D)
  let d := G.form.dualBasis G.nondegenerate e
  apply primeTemplate_commonKernel hζ a G.form d.equivFun e.equivFun
  · intro x y
    change (∑ i, d.equivFun x i * e.equivFun y i) = _
    conv_rhs => rw [← e.sum_repr y]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.equivFun_apply, d,
      LinearMap.BilinForm.dualBasis_repr_apply, mul_comm (e.repr y _)]
  · intro _
    have hdim := G.dim_pos
    have hsub : Fintype.card {k : Fin m // k ≠ j} = m - 1 := by
      simp
    simp only [PrimeCommonSpectators, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      ZMod.card, hsub, ← pow_add, axisFibers]
    congr 1
    have h := j.isLt
    have he : 2 * G.D - 1 + (m-1) + (m-1) = 2 * (m + G.D - 1) - 1 := by omega
    rw [← he]
    ring

/-- Explicit linear gate coefficient for the masked term, independent of both
the ring of coefficients and the length of a digit column. -/
theorem chargedRectangle_program (hζ : IsPrimitiveRoot ζ ℓ) {m : ℕ} {W : Type}
    [Fintype W] (R : ChargedRectangle L b (L / ℓ)) (z : K) (B : Matrix W W K)
    (a : (ZMod ℓ)ˣ) (j : Fin m) (f : ℕ) :
    ∃ n ≤ chargedRectangleOverhead (Fintype.card (chargedEndpoint R)) (Fintype.card (chargedEndpoint R))
      (Fintype.card W) 0 0 0 * Fintype.card (G.RowAddress m f),
      PrimeTemplateProgram ℓ f (G.axisFibers m f) ζ
        (routedRectangleMatrix (chargedEndpoint R) (chargedEndpoint R) z
          (routedPencilTerm B (G.transfer hζ f a j))) n (Fintype.card W * (2 * G.D)) := by
  classical
  let S := chargedEndpoint R
  let X := G.RowAddress m f
  let e := G.queryChart f j (fun _ _ => false)
  let g (v : BitLabel L b) : X ≃ X := (G.queryChart f j v).trans e.symm
  let M := primeCommonKernel (C := Fin f) (T := PrimeCommonSpectators (Fin f) j ℓ) hζ G.form a G.D
  let N := M.submatrix e e
  let post (w : S) := primeCommonScatter (K := K) (g w.val)
  let pre (v : S) := primeCommonGather (K := K) (g v.val)
  have hfac (w v : S) : G.transfer hζ f a j w v = post w * N * pre v :=
    (primeCommonChart_square_factor M e (G.queryChart f j w) (G.queryChart f j v)).symm
  have hN : PrimeTemplateProgram ℓ f (G.axisFibers m f) ζ N 0 (2 * G.D) :=
    (G.queryCommon_template hζ f a j).submatrix e e.toEmbedding
  exact routedChargedRectangle_program S S z B (G.transfer hζ f a j) post N pre hfac
    0 0 0 (fun v => by simpa [post] using (primeCommonScatter_free (K := K) (g v.val)))
    (fun v => by simpa [pre] using (primeCommonGather_free (K := K) (g v.val))) hN (Nat.zero_le _)

/-- A query term on one charged rectangle costs two calls per common dimension
per clock row, uniformly over all digit lengths. -/
theorem chargedRectangle_linearRowTemplate (hζ : IsPrimitiveRoot ζ ℓ) {m : ℕ} {W : Type}
    [Fintype W] (R : ChargedRectangle L b (L / ℓ)) (z : K) (B : Matrix W W K)
    (a : (ZMod ℓ)ˣ) (j : Fin m) :
    LinearRowTemplate ℓ (G.axisFibers m) ζ (G.RowAddress m)
      (fun f => routedRectangleMatrix (chargedEndpoint R) (chargedEndpoint R) z
        (routedPencilTerm B (G.transfer hζ f a j))) (Fintype.card W * (2 * G.D)) := by
  refine ⟨chargedRectangleOverhead (Fintype.card (chargedEndpoint R)) (Fintype.card (chargedEndpoint R))
    (Fintype.card W) 0 0 0, fun f _ => ?_⟩
  obtain ⟨n,hn,hp⟩ := G.chargedRectangle_program hζ R z B a j f
  exact ⟨n,hn,_,le_rfl,hp⟩

end BitRoutingGeometry
end

end

end FiniteFourier
end LinearAlgebra
end OAI
