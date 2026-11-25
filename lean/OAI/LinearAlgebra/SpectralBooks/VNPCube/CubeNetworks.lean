import OAI.LinearAlgebra.SpectralBooks.VNPCube.CubeWirePrice
import OAI.LinearAlgebra.SpectralBooks.SpectralCrossingShortening
import OAI.LinearAlgebra.SpectralBooks.Theorem

/-! # Replacing antipodal wires by ordinary sums on cube edges

The strict price gap gives a uniform number of copies through all tensor
powers. A summand is indexed by a copy and a word of oriented cube edges.
Choosing a large initial bit width amortizes all selector bits.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace VNPCube

open Crossing SiteTensor HyperbolicObstruction

noncomputable section

variable {F : Type*} [Field F]

/-- The concrete product of one width-`b` wire on each antipodal pair. -/
def oppositeRaw (F : Type*) [Field F] (n b : ℕ) : Raw.{0} (Vertex (n+1)) F :=
  Raw.finProduct (fun j => (oppositeWire ((Fintype.equivFin (Vertex n)).symm j) b).raw F)

private theorem ofRaw_oppositeRaw (n b : ℕ) : ofRaw (oppositeRaw F n b) = oppositeClass F n b := by
  rw [oppositeRaw, ofRaw_finProduct, oppositeClass]
  exact Equiv.prod_comp (Fintype.equivFin (Vertex n)).symm (fun i => ofRaw ((oppositeWire i b).raw F))

private theorem restriction_of_cube_price (n b₀ s : ℕ)
    (hs : (2:ℝ)^n * Real.sqrt (n+1) * b₀ < s)
    (curv : ∀ (X : Type) [MetricSpace X] [CompleteSpace X], SpectralPlacementPrices F X →
      IsGeodesic X → CATZero X) :
    ∃ K : ℕ, 0 < K ∧ ∀ h : ℕ, 0 < h →
      RestrictsWirePower (oppositeRaw F n (b₀*h)).coeff (fun e => edgeWire e s) K h := by
  have hw (e : Edge (n+1)) : ofRaw ((edgeWire e 1).raw F) ≠ 0 :=
    fun h => Wire.raw_coeff_ne_zero F _ ((ofRaw_eq_zero_iff _).mp h)
  obtain ⟨K,hK,H⟩ := strict_comparison_of_log_power_cover
    (strictSpectralComparison (Vertex (n+1)) F) _ (oppositeClass_ne_zero 1) hw b₀ (fun _ => s)
    (fun φ => by
      obtain ⟨e,hpos,hbound⟩ := exists_cube_edge_price curv φ
      refine ⟨e,?_⟩
      exact (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg b₀)).trans_lt
        (by linarith only [mul_lt_mul_of_pos_right hs hpos]))
  refine ⟨K,hK,fun h hh => restrictsWirePower_of_le _ _ _ _ ?_⟩
  have he (e : Edge (n+1)) : ofRaw ((edgeWire e s).raw F) = ofRaw ((edgeWire e 1).raw F) ^ s :=
    Wire.ofRaw_setWidth_eq_pow F (edgeWire e 1) s
  simpa only [ofRaw_oppositeRaw, oppositeClass_eq_pow (F := F) (b := b₀*h), pow_mul, he]
    using H h hh

/-- The target at some width above `B` is an ordinary sum of cube-edge
networks with selector rate at most `η` and total edge width at most
twice the antipodal count times the square root of the dimension times `b`. -/
def AdmitsAntipodalNetworks (F : Type*) [Field F] (n : ℕ) (η : ℝ) (B : ℕ) : Prop :=
    ∃ b K h s : ℕ, B < b ∧ 0 < K ∧ 0 < h ∧
      (Nat.clog 2 (K * Fintype.card (Edge (n+1)) ^ h) : ℝ) ≤ η * b ∧
      (h : ℝ) * s ≤ 2 * (2:ℝ)^n * Real.sqrt (n+1) * b ∧
      ∃ T : (k : Fin K) → (w : Fin h → Edge (n+1)) →
        LocalTables (B := (oppositeRaw F n b).Leg) (fun t => edgeWire (w t) s) F,
        ∀ x, (oppositeRaw F n b).coeff x =
          ∑ k, ∑ w, network (fun t => edgeWire (w t) s) (T k w) x

/-- The precise ordinary network, width and selector conclusion of the
companion's antipodal-wire lemma on a cube of positive dimension `n + 1`. -/
theorem exists_antipodal_networks_of_curvature (n : ℕ) {η : ℝ} (hη : 0 < η)
    (curv : ∀ (X : Type) [MetricSpace X] [CompleteSpace X], SpectralPlacementPrices F X →
      IsGeodesic X → CATZero X) (B : ℕ) :
    AdmitsAntipodalNetworks F n η B := by
  let J := Fintype.card (Edge (n+1))
  let t := Nat.clog 2 J
  obtain ⟨m,hm⟩ := exists_nat_gt (((t : ℝ)+1)/η)
  have hrate : (t : ℝ)+1 < η*m := by
    simpa [mul_comm] using (div_lt_iff₀ hη).mp hm
  have hm0 : 0 < m := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, Nat.cast_zero, mul_zero] at hrate
    linarith [Nat.cast_nonneg t (α := ℝ)]
  let c := (2:ℝ)^n * Real.sqrt (n+1)
  have hc : 1 ≤ c := by
    have h1 : 1 ≤ Real.sqrt (n+1) := Real.one_le_sqrt.mpr (by linarith [Nat.cast_nonneg n (α := ℝ)])
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) h1
  let s := ⌊c*m⌋₊ + 1
  have h₁ : c*m < s := by exact_mod_cast Nat.lt_floor_add_one (c*m)
  have h₂ : (s:ℝ) ≤ 2*(c*m) := by
    have hcm : 1 ≤ c*m := one_le_mul_of_one_le_of_one_le hc (by exact_mod_cast hm0)
    have hl := Nat.floor_le (show 0 ≤ c*m by positivity)
    dsimp [s]
    push_cast
    linarith
  obtain ⟨K,hK,H⟩ := restriction_of_cube_price n m s h₁ curv
  let h := Nat.clog 2 K + B + 1
  have hh : 0 < h := Nat.succ_pos _
  have hK' : Nat.clog 2 K ≤ h := by dsimp [h]; omega
  refine ⟨m*h,K,h,s,?_,hK,hh,?_,?_,?_⟩
  · have : B < h := by dsimp [h]; omega
    exact this.trans_le (Nat.le_mul_of_pos_left h hm0)
  · have hbits : Nat.clog 2 (K * J^h) ≤ Nat.clog 2 K + t*h := by
      apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
      rw [pow_add 2 (Nat.clog 2 K) (t*h), pow_mul 2 t h]
      exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) K)
        (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) J) h)
    change (Nat.clog 2 (K*J^h) : ℝ) ≤ _
    calc
      _ ≤ ((h + t*h : ℕ) : ℝ) := by exact_mod_cast hbits.trans (Nat.add_le_add_right hK' _)
      _ = ((t:ℝ)+1)*h := by push_cast; ring
      _ ≤ _ := by push_cast; nlinarith only [mul_le_mul_of_nonneg_right hrate.le (Nat.cast_nonneg h)]
  · push_cast
    calc
      (h:ℝ) * s ≤ h * (2 * (c*m)) := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg h)
      _ = _ := by dsimp [c]; ring
  · exact restriction_copiesOfWirePower _ _ (H h hh)

/-- Antipodal wires on the cube. Over every field, for arbitrarily large bit
widths, ordinary sums of edge networks attain the stated selector and width
bounds. In particular this holds over the prime field used by the companion. -/
theorem exists_antipodal_networks (F : Type*) [Field F] (n : ℕ) {η : ℝ} (hη : 0 < η)
    (B : ℕ) : AdmitsAntipodalNetworks F n η B :=
  exists_antipodal_networks_of_curvature n hη (fun _ _ _ P hg => P.catZero hg) B

end
end VNPCube

end SpectralBooks
end LinearAlgebra
end OAI
