import OAI.LinearAlgebra.FiniteFourier.BatchedProjective
import OAI.LinearAlgebra.FiniteFourier.BatchedDictionary
import OAI.LinearAlgebra.FiniteFourier.BatchedTwoMinors

/-! # Descent of the sparse dictionary bound through successive row quotients -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open Matrix MvPolynomial
open scoped Classical NNReal
noncomputable section

variable {K : Type*} [Field K] {R C : Type} [Fintype R] [Fintype C]

def rowElimination (i : R) (z : R → K) : Matrix R R K :=
  1 - vecMulVec z (Pi.single i 1)

theorem rank_loss_rowElimination (Q : Matrix R R K) (i : R) (z : R → K) :
    Q.rank ≤ (Q * rowElimination i z).rank + 1 := by
  let D := vecMulVec z (Pi.single i 1)
  have he : Q * rowElimination i z + Q * D = Q := by
    rw [← Matrix.mul_add]
    simp [rowElimination, D]
  have h := matrix_rank_add_le (Q * rowElimination i z) (Q * D)
  rw [he] at h
  exact h.trans (Nat.add_le_add_left ((rank_mul_le_right _ _).trans (rank_vecMulVec_le _ _)) _)

private theorem rank_drop_of_killed (B : Matrix R C K) (E : Matrix R R K)
    (v : LinearMap.range B.mulVecLin) (hv : v ≠ 0) (hk : E *ᵥ v.val = 0) :
    (E * B).rank < B.rank := by
  let g := E.mulVecLin.domRestrict (LinearMap.range B.mulVecLin)
  have hm : v ∈ LinearMap.ker g := hk
  have hpos : 0 < Module.finrank K (LinearMap.ker g) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hm⟩, fun h => hv (congrArg Subtype.val h)⟩
  have he : (E * B).rank = Module.finrank K (LinearMap.range g) := by
    rw [Matrix.rank, Matrix.mulVecLin_mul, LinearMap.range_comp]
    exact congrArg (fun W : Submodule K (R → K) => Module.finrank K W)
      (LinearMap.range_domRestrict _ _).symm
  rw [he, Matrix.rank, ← g.finrank_range_add_finrank_ker]
  exact Nat.lt_add_of_pos_right hpos

theorem exists_rank_dropping_vector [Nonempty R] (B : Matrix R C K) {r : ℕ}
    (hr : B.rank ≤ r + 1) :
    ∃ v : R → K, (∃ i, v i ≠ 0) ∧ ∀ i, v i ≠ 0 →
      (rowElimination i (fun j => v j / v i) * B).rank ≤ r := by
  by_cases hsmall : B.rank ≤ r
  · exact ⟨fun _ => 1, ⟨Classical.arbitrary R, one_ne_zero⟩,
      fun _ _ => (rank_mul_le_right _ _).trans hsmall⟩
  have hpos : 0 < B.rank := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank K (LinearMap.range B.mulVecLin) from hpos)
  refine ⟨v.val, ?_, fun i hi => ?_⟩
  · by_contra! h
    exact hv (Subtype.ext (funext h))
  · have hk : rowElimination i (fun j => v.val j / v.val i) *ᵥ v.val = 0 := by
      rw [rowElimination, sub_mulVec, one_mulVec, vecMulVec_mulVec, single_dotProduct, one_mul]
      funext j
      change v.val j - v.val j / v.val i * v.val i = 0
      rw [div_mul_cancel₀ _ hi, sub_self]
    exact Nat.le_of_lt_succ ((rank_drop_of_killed B _ v hv hk).trans_le hr)

private theorem rowElimination_specialization [IsAlgClosed K] [Nonempty R]
    {S : Type*} (A : S → Matrix R C K) (v : S → R → K) (hv : ∀ s, ∃ i, v s i ≠ 0)
    (M : Matrix R C K) (hM : matrixPoint M ∈ affineZariskiClosure (Set.range (matrixPoint ∘ A)))
    (T : Set (Matrix R C K)) (hT : ∀ s i, v s i ≠ 0 →
      rowElimination i (fun j => v s j / v s i) * A s ∈ T) :
    ∃ (i : R) (z : R → K), matrixPoint (rowElimination i z * M) ∈
      affineZariskiClosure (matrixPoint '' T) := by
  obtain ⟨i, z, _, hz⟩ := projective_chart_specialization (matrixPoint ∘ A) v hv (matrixPoint M) hM
  let p (rc : R × C) : MvPolynomial ((R × C) ⊕ R) K :=
    X (.inl rc) - X (.inr rc.1) * X (.inl (i, rc.2))
  have he (U : Matrix R C K) (w : R → K) :
      (fun rc => eval (Sum.elim (matrixPoint U) w) (p rc)) =
        matrixPoint (rowElimination i w * U) := by
    funext ⟨r,c⟩
    simp [p, matrixPoint, rowElimination, Matrix.sub_mul, vecMulVec_mul, single_vecMul]
    rfl
  refine ⟨i, z, ?_⟩
  rw [← he]
  apply mapsTo_affineZariskiClosure_of_polynomial p _ hz
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨_, hT s i hs, (he (A s) _).symm⟩

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))

def rankListLocus (R C : Type) [Fintype R] [Fintype C] (r : ℕ) (b : ℝ≥0) :
    Set (Matrix R C K) :=
  {A | ∃ B U : Matrix R C K, B.rank ≤ r ∧ listValue φ U ≤ b ∧ A = B + U}

theorem exists_row_quotient_of_list_border [IsAlgClosed K] [Nonempty R]
    (r : ℕ) (b : ℝ≥0) (M : Matrix R C K)
    (hM : matrixPoint M ∈ affineZariskiClosure (matrixPoint '' rankListLocus φ R C r b)) :
    ∃ Q : Matrix R R K, Fintype.card R ≤ Q.rank + r ∧ listValue φ (Q * M) ≤ b := by
  induction r generalizing M with
  | zero =>
    refine ⟨1, by simp, ?_⟩
    rw [Matrix.one_mul]
    apply listValue_le_of_mem_closure φ hM
    rintro _ ⟨B, U, hB, hU, rfl⟩
    have hbot := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hB :
      Module.finrank K (LinearMap.range B.mulVecLin) = 0)
    have he : B = 0 := by
      apply Matrix.toLin'.injective
      rw [map_zero]
      exact LinearMap.range_eq_bot.mp hbot
    simpa [he] using hU
  | succ r ih =>
    let S := rankListLocus φ R C (r + 1) b
    choose B U hB hU he using (fun s : S => show ∃ B U : Matrix R C K,
      B.rank ≤ r + 1 ∧ listValue φ U ≤ b ∧ s.val = B + U from s.property)
    choose v hv hdrop using fun s => exists_rank_dropping_vector (B s) (hB s)
    have hrange : Set.range (matrixPoint ∘ (Subtype.val : S → Matrix R C K)) =
        matrixPoint '' S := by rw [Set.range_comp, Subtype.range_coe]
    obtain ⟨i, z, hz⟩ := rowElimination_specialization (Subtype.val : S → Matrix R C K)
      v hv M (by rw [hrange]; exact hM) (rankListLocus φ R C r b) (by
        intro s i hi
        let E := rowElimination i (fun j => v s j / v s i)
        exact ⟨E * B s, E * U s, hdrop s i hi, (listValue_mul_le φ E _).trans (hU s),
          by rw [he s, Matrix.mul_add]⟩)
    obtain ⟨Q, hQ, hval⟩ := ih _ hz
    refine ⟨Q * rowElimination i z, ?_, by rw [Matrix.mul_assoc]; exact hval⟩
    have := rank_loss_rowElimination Q i z
    omega

def rankSparseLocus (R C K : Type*) [Field K] [Fintype R] [Fintype C] (r : ℕ) (T : ℝ) :
    Set (Matrix R C K) :=
  {A | ∃ B U : Matrix R C K, B.rank ≤ r ∧ (matrixEntryCount U : ℝ) ≤ T ∧ A = B + U}

theorem exists_row_quotient_of_sparse_border [IsAlgClosed K] [Nonempty R]
    (P : SpectralPlacementPrices K Plane)
    (hflat : ∀ (s : Finset Plane) (hs : s.Nonempty), P.diagonal s = meanWidth s hs)
    {x a b : Plane} {δ : ℝ} (hp : PricesListsAt P φ x a b δ) (hd : 0 < δ)
    (hlen : dist a b ≤ δ) (r : ℕ) (T : ℝ) (hT : 0 ≤ T) (M : Matrix R C K)
    (hM : matrixPoint M ∈ affineZariskiClosure (matrixPoint '' rankSparseLocus R C K r T)) :
    ∃ Q : Matrix R R K, Fintype.card R ≤ Q.rank + r ∧
      (listValue φ (Q * M) : ℝ) ≤ (Fintype.card R : ℝ) *
        (T / Fintype.card R) ^ (dist a b / δ) := by
  let bound : ℝ≥0 := ⟨(Fintype.card R : ℝ) * (T / Fintype.card R) ^ (dist a b / δ),
    by positivity⟩
  apply exists_row_quotient_of_list_border φ r bound M
  intro p h
  apply hM p
  rintro _ ⟨_, ⟨B, U, hB, hU, rfl⟩, rfl⟩
  apply h
  refine ⟨_, ⟨B, U, hB, ?_, rfl⟩, rfl⟩
  have hdic := listValue_dictionary_le φ P hflat hp hd hlen (1 : Matrix R R K) U
  rw [Matrix.one_mul] at hdic
  apply NNReal.coe_le_coe.mp
  refine hdic.trans ?_
  change _ ≤ (Fintype.card R : ℝ) * (T / Fintype.card R) ^ (dist a b / δ)
  gcongr

end
end FiniteFourier
end LinearAlgebra
end OAI
