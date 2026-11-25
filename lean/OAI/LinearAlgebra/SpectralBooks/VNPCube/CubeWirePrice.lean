import OAI.LinearAlgebra.SpectralBooks.VNPCube.CubeShortening
import OAI.LinearAlgebra.SpectralBooks.SpectralAxisComparison
import OAI.LinearAlgebra.SpectralBooks.GeodesicExtension
import OAI.LinearAlgebra.SpectralBooks.Curvature

/-! # The strict price gap between antipodal and coordinate wires -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace VNPCube

open SiteTensor Crossing HyperbolicObstruction

noncomputable section

variable {n : ℕ} {F : Type*} [Field F]

/-- One wire for each antipodal pair. -/
def oppositeWire (r : Vertex n) (b : ℕ) : Wire (Vertex (n+1)) where
  left := base r
  right := base r + 1
  distinct he := by
    have hh := congrFun he 0
    simp [base] at hh
  width := b

/-- We may list an edge in either orientation. -/
abbrev Edge (a : ℕ) := Vertex a × Fin a

def edgeWire {a : ℕ} (e : Edge a) (b : ℕ) : Wire (Vertex a) where
  left := e.1
  right := e.1 + unit e.2
  distinct he := by
    have hh := congrFun he e.2
    simp [unit] at hh
  width := b

/-- In a nonconstant CAT(0) placement some cube edge has positive length. -/
theorem exists_positive_edge {a : ℕ} {X : Type*} [MetricSpace X] (h : CATZero X)
    (y : Vertex a → X) (hy : ∃ x z, 0 < dist (y x) (y z)) :
    ∃ e : Edge a, 0 < dist (y e.1) (y (e.1 + unit e.2)) := by
  by_contra! hd
  have hzero (x : Vertex a) (i : Fin a) : dist (y x) (y (x+unit i)) = 0 :=
    (hd (x,i)).antisymm dist_nonneg
  obtain ⟨x,z,hxz⟩ := hy
  have hu := energy_le_edges y h (z-x)
  simp [energy, hzero] at hu
  have hle := Finset.single_le_sum (f := fun t => dist (y t) (y (t+(z-x)))^2)
    (fun t _ => sq_nonneg _) (Finset.mem_univ x)
  rw [show x+(z-x)=z by abel] at hle
  linarith [sq_pos_of_pos hxz]

/-- The unit-width antipodal network class is the tensor product of its wires. -/
def oppositeClass (F : Type*) [Field F] (n b : ℕ) : TensorClass.{0} (Vertex (n+1)) F :=
  ∏ r : Vertex n, ofRaw ((oppositeWire r b).raw F)

theorem oppositeClass_ne_zero (b : ℕ) : oppositeClass F n b ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro r _
  exact fun h => Wire.raw_coeff_ne_zero F _ ((ofRaw_eq_zero_iff _).mp h)

theorem oppositeClass_eq_pow (b : ℕ) : oppositeClass F n b = oppositeClass F n 1 ^ b := by
  unfold oppositeClass
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => Wire.ofRaw_setWidth_eq_pow F (oppositeWire i 1) b

private theorem log_opposite (φ : normalizedSpectrum (S := TensorClass.{0} (Vertex (n+1)) F)
    (· ≤ ·)) : Real.logb 2 (φ.val (oppositeClass F n 1) : ℝ) =
      ∑ r, Real.logb 2 (φ.val (ofRaw ((oppositeWire r 1).raw F)) : ℝ) := by
  change Real.logb 2 ((normalizedSpectrum.toRingHom φ) (oppositeClass F n 1) : ℝ) = _
  rw [oppositeClass, map_prod, NNReal.coe_prod]
  apply Real.logb_prod
  intro r _
  apply ne_of_gt
  apply NNReal.coe_pos.mpr
  apply spectral_value_pos φ
  exact fun h => Wire.raw_coeff_ne_zero F _ ((ofRaw_eq_zero_iff _).mp h)

/-- Exact price bound for a normalized point in the finite cube tensor
semiring, together with positivity of its witnessing edge. -/
theorem exists_cube_edge_price
    (curv : ∀ (X : Type) [MetricSpace X] [CompleteSpace X], SpectralPlacementPrices F X →
      IsGeodesic X → CATZero X)
    (φ : normalizedSpectrum (S := TensorClass.{0} (Vertex (n+1)) F) (· ≤ ·)) :
    ∃ e : Edge (n+1),
      let m := Real.logb 2 (φ.val (ofRaw ((edgeWire e 1).raw F)) : ℝ)
      0 < m ∧ Real.logb 2 (φ.val (oppositeClass F n 1) : ℝ) ≤ (2:ℝ)^n * Real.sqrt (n+1) * m := by
  classical
  obtain ⟨X, met, P, y, hc, hg, _, hp⟩ := SpectralPlacementPrices.realize_finite_point_geodesic φ 1 zero_le_one
  let := met
  let := hc
  have cat := curv X P hg
  have hold (T : Raw.{0} (Vertex (n+1)) F) (_hT : T.coeff ≠ 0) :
      P.price T y = Real.logb 2 (φ.val (ofRaw T) : ℝ) := by
    have he := ofRaw_eq_iff.mpr (Raw.group_id_equivalent T)
    simpa only [Function.comp_id, rawLogPrice, one_mul, he] using hp T id
  let D := Raw.diagonal (Vertex (n+1)) F (Fin 2)
  have hdiag : 0 < P.price D y := by
    have hD : D.coeff ≠ 0 := by
      intro hz
      have hh := congrFun hz (fun _ => (0 : Fin 2))
      change (Raw.diagonal (Vertex (n+1)) F (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0 : F) at hh
      rw [Raw.diagonal_coeff_at 0] at hh
      simp at hh
    rw [hold _ hD, show D = Raw.diagonal (Vertex (n+1)) F (Fin 2) from rfl,
      ofRaw_diagonal_fin_eq_natCast]
    change 0 < Real.logb 2 ((normalizedSpectrum.toRingHom φ) (2 : TensorClass.{0} _ F) : ℝ)
    norm_num [map_ofNat, Real.logb_self_eq_one]
  let d (e : Edge (n+1)) := dist (y e.1) (y (e.1 + unit e.2))
  obtain ⟨e, _, hmax⟩ := Finset.univ.exists_max_image d Finset.univ_nonempty
  have hm (x : Vertex (n+1)) (i : Fin (n+1)) : dist (y x) (y (x+unit i)) ≤ d e :=
    hmax (x,i) (Finset.mem_univ _)
  obtain ⟨j,hj⟩ := exists_positive_edge cat y (P.exists_dist_pos_of_diagonal_pos y hdiag)
  have he : d e = Real.logb 2 (φ.val (ofRaw ((edgeWire e 1).raw F)) : ℝ) :=
    dist_eq_wire_price φ P y hold (edgeWire e 1)
  refine ⟨e, he ▸ hj.trans_le (hm _ _), ?_⟩
  rw [log_opposite, ← he]
  have eqs (r : Vertex n) : dist (y (base r)) (y (base r + 1)) =
      Real.logb 2 (φ.val (ofRaw ((oppositeWire r 1).raw F)) : ℝ) :=
    dist_eq_wire_price φ P y hold (oppositeWire r 1)
  simpa only [eqs] using antipodal_sum_le y cat (show 0 ≤ d e from dist_nonneg) hm

end
end VNPCube

end SpectralBooks
end LinearAlgebra
end OAI
