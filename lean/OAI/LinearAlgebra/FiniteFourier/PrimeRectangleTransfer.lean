import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleGeometry
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonCoordinates
import OAI.LinearAlgebra.FiniteFourier.PrimeSpectrumEquiv
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleSystem

/-! # Common-coordinate transfers between ordinary query arrays -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
namespace BitRoutingGeometry

variable {ℓ L b : ℕ} [Fact ℓ.Prime] (G : BitRoutingGeometry ℓ L b)

theorem dim_pos : 0 < G.D := by
  by_contra! h
  have : IsEmpty (Fin G.D) := Fin.isEmpty_iff.mpr (Nat.eq_zero_of_le_zero h)
  let v : BitLabel L b := fun _ _ => false
  have hv := G.vector_self v
  have he : G.vector v = 0 := Subsingleton.elim _ _
  simp [he] at hv

/-- The ordinary coordinates of a paired row in the pencil. -/
abbrev RowAddress (m f : ℕ) := PrimeSpectrumDigits (Fin f × (Fin m ⊕ Fin (G.D-1))) ℓ

/-- Number of independent fibers in each recursive axis call on this row. -/
abbrev axisFibers (m f : ℕ) := ℓ ^ ((2 * (m + G.D - 1) - 1) * f)

/-- Move the ordinary active slots and spectators into common coordinates. -/
def queryChart {m : ℕ} (f : ℕ) (j : Fin m) (v : BitLabel L b) :=
  primeCommonQueryChart (C := Fin f) j
    (primeCommonLabelMap (G.labelCharts v).first) (primeCommonLabelMap (G.labelCharts v).second)

/-- Common kernel in the target and source label charts, including transfers between labels. -/
def transfer {K : Type*} [CommRing K] [Invertible (ℓ : K)] {ζ : K}
    (hζ : IsPrimitiveRoot ζ ℓ) {m : ℕ} (f : ℕ) (a : (ZMod ℓ)ˣ) (j : Fin m)
    (w v : BitLabel L b) : Matrix (G.RowAddress m f) (G.RowAddress m f) K :=
  (primeCommonKernel (C := Fin f) (T := PrimeCommonSpectators (Fin f) j ℓ) hζ G.form a G.D).submatrix
    (G.queryChart f j w) (G.queryChart f j v)

/-- The row volume equals the number of entries of the corresponding digit transform. -/
theorem card_rowAddress (m f : ℕ) : Fintype.card (G.RowAddress m f) = ℓ ^ (2 * (m + G.D - 1) * f) := by
  have hd := G.dim_pos
  simp only [RowAddress, PrimeSpectrumDigits, Fintype.card_prod, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, Fintype.card_sum, ← pow_add]
  congr 1
  rw [show m + G.D - 1 = m + (G.D - 1) by omega]
  ring

end BitRoutingGeometry

/-- Use the routing system's diagonal Gram realization in the endpoint charts. -/
def PrimeRectangleSystem.geometry {K : Type*} [CommRing K] {ℓ L b : ℕ} [Fact ℓ.Prime]
    (S : PrimeRectangleSystem K ℓ L b) : BitRoutingGeometry ℓ L b := by
  let B := Matrix.toBilin' (Matrix.diagonal S.a)
  have eval (x y : Fin S.D → ZMod ℓ) : B x y = ∑ i, S.a i * x i * y i := by
    simp [B, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal, mul_assoc, mul_left_comm]
  have symm : B.IsSymm := ⟨fun x y => by simp [eval, mul_right_comm]⟩
  have sep : B.SeparatingLeft := by
    intro x hx
    funext i
    have h := hx (Pi.single i 1)
    simp [eval, Pi.single_apply, mul_ite] at h
    exact h.resolve_left (S.diagonal_ne_zero i)
  exact ⟨S.D, S.dimension_le, B, symm,
    ⟨sep, fun y hy => sep y fun x => (symm.eq y x).trans (hy x)⟩, S.d,
    fun v w => (eval _ _).trans (S.gram v w)⟩

end

end

end FiniteFourier
end LinearAlgebra
end OAI
