import OAI.LinearAlgebra.FiniteFourier.GridStageCost
import OAI.LinearAlgebra.FiniteFourier.WorkingGridWord
import OAI.LinearAlgebra.FiniteFourier.UpperWorkspace

/-! # Small-group complexity of geometric grids over arbitrary fields

The common cyclotomic extension accommodates every auxiliary root of unity.
Its degree fits within the number of complementary fibers. The occupied word
acts on at most 170 times the group volume, yielding uniform bounds over the
ground field after the packed descent.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter
open scoped BigOperators

universe v

private lemma workingRegisters_le_total {B N : ℕ} (hN : 170 ^ 2 ≤ N) (hB : B^12 ≤ N) :
    170 * B ≤ N := by
  by_cases h : B < 170
  · exact (Nat.mul_le_mul_left _ h.le).trans hN
  have h' : 170 ≤ B := by omega
  calc
    _ ≤ B * B := Nat.mul_le_mul_right B h'
    _ = B^2 := (sq B).symm
    _ ≤ B^12 := Nat.pow_le_pow_right (by omega) (by decide)
    _ ≤ N := hB

/-- Every sufficiently large global size admits the uniform small-group
estimate, including groups whose order shares factors with the characteristic. -/
theorem eventually_smallGridCost {β α C : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hβα : β < α) (hC : 0 < C) :
    ∃ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (K : Type v) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι]
        (a : ι → ℕ) (A : ∀ i, Matrix (Fin (a i)) (Fin (a i)) K),
        FixedConvolutionBound K β C → ShearTensorBound K β C →
        (∀ i, 2 ≤ a i) → (∀ i, GridFactor (A i)) → (∏ i, a i)^12 ≤ N →
        (complexity (Matrix.blockDiagonal (fun _ : Fin (N / (∏ i, a i)) => gridTensor A)) : ℝ) ≤
          D * N * (1 + Real.logb 2 N)^α := by
  let C₁ := (7*C + 1) * 170
  let D₁ := 2 * ((workingGridDepthConstant : ℝ) + 1)
  let Q := 2 * C₁ * D₁ * (1 + 1 / ((α-β) * Real.log 2))
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hD₁ : 0 < D₁ := by dsimp [D₁]; positivity
  have hQ : 0 < Q := by dsimp [Q]; have := sub_pos.mpr hβα; positivity
  refine ⟨Q * (2 : ℝ)^α, by positivity, ?_⟩
  filter_upwards [eventually_exists_workingGroup, eventually_ge_atTop (170^2 : ℕ)] with N hroot hN
  intro K _ ι _ _ a A hconv hshear ha hA hsize
  classical
  let B := ∏ i, a i
  let t := Nat.clog 2 N
  let X := ∀ i, Fin (a i)
  let W := Fin (169 * B)
  let h := N / B
  have hB : 0 < B := Finset.prod_pos (fun i _ => lt_of_lt_of_le (by decide) (ha i))
  have hNpos : 0 < N := by omega
  have hX : Fintype.card X = B := by simp [X, B, Fintype.card_pi]
  have hJ : Fintype.card (X ⊕ W) = 170 * B := by simp [W, hX]; omega
  obtain ⟨w, hdeg, horder, hcapacity⟩ := hroot K ι a ha hsize
  let E := CyclotomicField w.order K
  let : NeZero (w.order : K) := ⟨w.order_cast_ne_zero⟩
  let : NeZero w.order := NeZero.of_neZero_natCast K
  obtain ⟨ζ, hζ, -, -⟩ := w.exists_roots
  let pb : PowerBasis K E := hζ.powerBasis K
  have hcap : pb.dim ≤ h := pb.finrank ▸ hdeg.trans (horder.trans hcapacity)
  have hlogN : Real.logb 2 N ≤ t := by
    rw [show t = ⌈Real.logb (2 : ℕ) N⌉₊ by exact (Real.natCeil_logb_natCast 2 N).symm]
    exact Nat.le_ceil _
  have hlog {k : ℕ} (hk : 0 < k) (hkn : k ≤ N) : Real.logb 2 k ≤ t :=
    (Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hk) (by exact_mod_cast hkn)).trans hlogN
  have he := hlog pb.dim_pos (hcap.trans (Nat.div_le_self ..))
  have hsp := hlog (hJ ▸ Nat.mul_pos (by decide) hB)
    (hJ ▸ workingRegisters_le_total hN hsize)
  obtain ⟨mc, sc, hm, hs, hstage⟩ := grid_stage_cost (I := X ⊕ W) pb hβ hβ' hC.le hconv hshear
    (hJ ▸ Nat.mul_pos (by decide) hB) he hsp
  rw [hJ, Nat.cast_mul, Nat.cast_ofNat] at hstage
  have hstage' : ((mc+sc : ℕ) : ℝ) ≤ C₁ * pb.dim * B * (1+(t : ℝ))^β := by
    dsimp [C₁]
    linarith only [hstage]
  let T := gridTensor A
  let T' : Matrix (X ⊕ W) (X ⊕ W) K := Matrix.fromBlocks T 0 0 1
  let d := workingGridDepthConstant * (1 + Nat.clog 2 (1+t))
  have hw : LayerWord d (T'.map (algebraMap K E)) := by
    simpa [T', T, Matrix.fromBlocks_map] using w.grid_word ha hA
  have hlogt : 0 ≤ Real.logb 2 (1 + (t : ℝ)) := Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) t])
  have hdepth : (d : ℝ) ≤ D₁ * (1+Real.logb 2 (1+(t : ℝ))) := by
    rw [show (d : ℝ) = (workingGridDepthConstant : ℝ) * (↑(1+Nat.clog 2 (1+t)) : ℝ) by
      simp [d]]
    have hd := mul_le_mul_of_nonneg_left (clog_depth_le t) (Nat.cast_nonneg workingGridDepthConstant (α := ℝ))
    dsimp [D₁]
    linarith only [hd, hlogt]
  have hcost := grid_group_descent pb.basis T' (h := h) (by simpa using pb.dim_pos)
    (by simpa using hcap) hw hm hs (B := (B : ℝ)) (Nat.cast_nonneg _) hC₁.le hD₁.le
    (Nat.cast_nonneg t) hβα hdepth (by simpa only [Fintype.card_fin] using hstage')
  change (complexity (Matrix.blockDiagonal fun _ : Fin h => T') : ℝ) ≤
    Q * ((h : ℝ) * B) * (1+(t : ℝ))^α at hcost
  have hdata := complexity_data_of_batches (W := W) (D := Fin h) T
  have hNlog : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) (by exact_mod_cast hNpos)
  have ht : (1+(t : ℝ))^α ≤ (2 : ℝ)^α * (1 + Real.logb 2 N)^α := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    apply Real.rpow_le_rpow (by positivity) _ (hβ.trans hβα.le)
    linarith [real_clog_two_le N hNpos]
  have hhB : (h : ℝ) * B ≤ N := by exact_mod_cast Nat.div_mul_le_self N B
  calc
    _ ≤ (complexity (Matrix.blockDiagonal (fun _ : Fin h => T')) : ℝ) := by exact_mod_cast hdata
    _ ≤ _ := hcost
    _ ≤ Q * N * ((2 : ℝ)^α * (1+Real.logb 2 N)^α) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hhB hQ.le) ht (by positivity) (by positivity)
    _ = _ := by ring

end FiniteFourier
end LinearAlgebra
end OAI
