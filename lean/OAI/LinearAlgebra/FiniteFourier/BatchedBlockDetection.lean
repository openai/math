import OAI.LinearAlgebra.FiniteFourier.BatchedCoordinates
import OAI.LinearAlgebra.FiniteFourier.BatchedGeometry
import OAI.LinearAlgebra.FiniteFourier.BatchedBlockQuotient

/-! # Simultaneous detection of arbitrary Fourier blocks -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal Matrix
noncomputable section

variable {K F : Type*} [Field K] [Field F] {n J : ℕ}

def blockInputOutput (f : K →+* F) (B : FourierBlock K n) :=
  Matrix.fromCols (1 : Matrix (Fin n) (Fin n) F) (B.matrix.map f)ᵀ

private theorem symmetric_table_gram {G : Type} [AddCommGroup G] [Fintype G]
    (h : Admissible G F) (e : G ≃ Character G F) (i j : G) (hne : j ≠ -i) :
    let H := (fourierMatrix G F).submatrix e id
    (Hᵀ * H) i j = 0 := by
  change (∑ k, fourierMatrix G F (e k) i * fourierMatrix G F (e k) j) = 0
  rw [e.sum_comp (fun t => fourierMatrix G F t i * fourierMatrix G F t j)]
  exact (fourier_gram_entry G h i j).trans (ite_eq_right (Ne.symm hne))

theorem batch_rank_sparse_obstruction [IsAlgClosed F] [Nonempty (Fin J)]
    (P : SpectralPlacementPrices F Plane)
    (hflat : ∀ (s : Finset Plane) (hs : s.Nonempty), P.diagonal s = meanWidth s hs)
    (hnorm : ∀ L : ℝ, 0 < L →
      P.price (Raw.diagonal (Fin 4) F (Fin 2)) (rectangleSites L 1) = L+1)
    (hsat : ∀ (G : Type) [AddCommGroup G] [Fintype G], Admissible G F →
      ∀ (e : G ≃ Character G F) (L : ℝ), 0 < L →
      rectanglePrice (fourierPhasePrice P) ((fourierMatrix G F).submatrix e id) L 1 =
        (L + Real.sqrt (L^2 + 1^2)) * Real.logb 2 (Fintype.card G))
    (f : K →+* F) (B : Fin J → FourierBlock K n) (hn : 2 ≤ n)
    (hm : 1000 ≤ Real.sqrt (Real.logb 2 n))
    (r : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hr : (r : ℝ) ≤ (2:ℝ)^(-(100:ℤ)) * (J * (n:ℝ)) / 200)
    (ht : T ≤ J * (n:ℝ) * (2:ℝ) ^ (Real.sqrt (Real.logb 2 n) / 8)) :
    matrixPoint (Matrix.blockDiagonal (fun j => blockInputOutput f (B j))) ∉
      affineZariskiClosure (matrixPoint ''
        rankSparseLocus (Fin n × Fin J) ((Fin n ⊕ Fin n) × Fin J) F r T) := by
  let _ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let m := Real.logb 2 n
  let L := batchHeight m
  let δ := batchTriangle L
  let S : BatchScaleBounds m L δ (batchHubTriangle L) := batch_scale_bounds hm
  have hd : 0 < δ := lt_of_lt_of_le (by norm_num) S.half_le
  obtain ⟨φ, χ, hl, hright⟩ := exists_batch_triangle_points P hflat S.height_pos
  obtain ⟨ψ, hψ⟩ := exists_batch_rectangle_point P S.height_pos (hnorm _ S.height_pos)
  have hvert := (batch_vertical S.height_pos.le).1
  apply sparse_border_obstruction φ P hflat hl hd _ (show 0 < (2:ℝ)^(-(100:ℤ)) by positivity)
    r T hT
  · intro j Q hQ
    let A := B j
    let G := Shrink.{0} A.G
    let g : A.G ≃+ G := Shrink.addEquiv.symm
    have hcard : Fintype.card G = n := (Fintype.card_congr g.toEquiv).symm.trans A.card_group
    have had : Admissible G F := (A.admissible.map f).of_groupEquiv g
    obtain ⟨e, row, col, s, hs, hsymm, he⟩ := block_symmetric_coordinates A f
    let H := (fourierMatrix G F).submatrix e id
    have hprice : phasePointValue ψ H = (2:ℝ) ^ (2*δ * Real.logb 2 (Fintype.card G) / (L+1)) := by
      have hh := hsat G had e L S.height_pos
      change fourierPhasePrice P H (rectangleSites L 1) = _ at hh
      rw [hψ] at hh
      have hnz : H ≠ 0 := by
        intro hz
        have h := congrFun (congrFun hz (e.symm 1)) 0
        simp [H, fourierMatrix] at h
      have hpos : 0 < phasePointValue ψ H := by
        exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue ψ _ (phaseRaw_coeff_ne_zero.mpr hnz))
      have heq : 2*δ * Real.logb 2 (Fintype.card G) / (L+1) = Real.logb 2 (phasePointValue ψ H) := by
        apply (div_eq_iff (by linarith [S.height_pos] : L+1 ≠ 0)).mpr
        unfold δ batchTriangle
        rw [mul_comm (Real.logb 2 (phasePointValue ψ H)), hh]
        ring_nf
      rw [heq, Real.rpow_logb (by norm_num) (by norm_num) hpos]
    have hfull := full_list_detection P φ χ ψ hl hright hψ hd (by linarith [S.height_pos])
      S.ratio (by rw [hcard]; exact S.gap) H hsymm (fun i => -i) (symmetric_table_gram had e) hprice
    have hdet := projected_list_detection P φ hflat hl hd S.triangle_le
      (batch_hub_semiperimeter S.height_pos.le) S.hub_le batch_hub_dist
      (by rw [hcard]; exact S.excess) H (Q.submatrix row row) hfull (by
        rw [Matrix.rank_submatrix, hcard]
        simpa using hQ)
    rw [hcard] at hdet
    rw [Fintype.card_fin]
    exact hdet.trans (NNReal.coe_le_coe.mpr
      (listValue_augmented_reindex φ (A.matrix.map f)ᵀ Q H row col s hs he))
  · simpa using hr
  · rw [Fintype.card_fin, hvert]
    apply le_trans _ (batch_dictionary_exponent hm)
    apply Real.rpow_le_rpow (by positivity) _ (div_nonneg S.height_pos.le hd.le)
    have hJ : 0 < J := Fin.pos_iff_nonempty.mpr inferInstance
    exact (div_le_iff₀ (by positivity : 0 < (J:ℝ)*n)).mpr (by rw [mul_comm]; exact ht)
  · rw [hvert]
    linarith [S.height_le, S.half_le]

end
end FiniteFourier
end LinearAlgebra
end OAI
