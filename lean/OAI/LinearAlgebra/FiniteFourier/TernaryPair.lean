import OAI.LinearAlgebra.FiniteFourier.TernaryFourierWord
import OAI.LinearAlgebra.FiniteFourier.GridInputs

/-! # Applying ternary shear words on pairs of binary coordinates -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped Kronecker
noncomputable section
variable {K : Type*} [CommRing K]

private theorem padTernary_transvection (a : K) :
    padTernary (Matrix.transvection (0 : Fin 3) 1 a) =
      Matrix.transvection (Sum.inl 0 : Fin 3 ⊕ Unit) (.inl 1) a := by
  ext (i|i) (j|j) <;> simp [padTernary, Matrix.fromBlocks, Matrix.transvection,
    Matrix.one_apply, Matrix.single_apply]

private theorem equiv_pair {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (hc : Fintype.card I = Fintype.card J) {a b : I} {u v : J} (hab : a ≠ b) (huv : u ≠ v) :
    ∃ e : I ≃ J, e a = u ∧ e b = v := by
  let e := Fintype.equivOfCardEq hc
  let f := e.trans (Equiv.swap (e a) u)
  have hfa : f a = u := by simp [f]
  have hne : u ≠ f b := by rw [← hfa]; exact f.injective.ne hab
  exact ⟨f.trans (Equiv.swap (f b) v), by simpa [hfa] using Equiv.swap_apply_of_ne_of_ne hne huv,
    by simp⟩

private theorem pairTransvection_cost {ζ : K} {t : ℕ}
    (hw : TernaryFourierWord ζ t (Matrix.transvection (0 : Fin 3) 1 (1 : K)))
    (n : ℕ) (a b : Fin 2 × Fin 2) (hab : a ≠ b) :
    RealizableAtMost (gridTensor (fun _ : Fin n => Matrix.transvection a b (1 : K)))
      (t * complexity (gridTensor (fun _ : Fin n => ternarySectorStage ζ))) := by
  obtain ⟨e, ha, hb⟩ := equiv_pair (I := Fin 2 × Fin 2) (J := Fin 3 ⊕ Unit)
    (by decide) hab (show (Sum.inl (0 : Fin 3) : Fin 3 ⊕ Unit) ≠ .inl 1 by decide)
  let f := Equiv.piCongrRight fun _ : Fin n => e
  have h := (hw.padded_cost n).submatrix f f.toEmbedding
  convert h using 1
  ext x y
  rw [Matrix.submatrix_apply]
  unfold gridTensor
  apply Finset.prod_congr rfl
  intro i _
  change Matrix.transvection a b (1 : K) (x i) (y i) =
    padTernary (Matrix.transvection (0 : Fin 3) 1 (1 : K)) (e (x i)) (e (y i))
  rw [padTernary_transvection, ← ha, ← hb]
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

private theorem pairedShear_factor :
    unitShear K ⊗ₖ unitShear K =
      Matrix.transvection (0, 0) (0, 1) 1 * Matrix.transvection (1, 0) (1, 1) 1 *
      Matrix.transvection (0, 0) (1, 0) 1 * Matrix.transvection (0, 1) (1, 1) 1 := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [unitShear, Matrix.transvection, Matrix.kronecker_apply, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]

private theorem pairedShear_cost {ζ : K} {t : ℕ}
    (hw : TernaryFourierWord ζ t (Matrix.transvection (0 : Fin 3) 1 (1 : K))) (n : ℕ) :
    RealizableAtMost (gridTensor (fun _ : Fin n => unitShear K ⊗ₖ unitShear K))
      (4 * (t * complexity (gridTensor (fun _ : Fin n => ternarySectorStage ζ)))) := by
  simp_rw [pairedShear_factor]
  rw [gridTensor_mul, gridTensor_mul, gridTensor_mul]
  have h := (((pairTransvection_cost hw n (0, 0) (0, 1) (by decide)).mul
    (pairTransvection_cost hw n (1, 0) (1, 1) (by decide))).mul
    (pairTransvection_cost hw n (0, 0) (1, 0) (by decide))).mul
    (pairTransvection_cost hw n (0, 1) (1, 1) (by decide))
  convert h using 1
  omega

/-- Splitting a binary word into two equal halves groups its entries into pairs.
Four conjugates of the local transvection implement the shear on each pair. -/
theorem complexity_shear_paired {ζ : K} {t : ℕ}
    (hw : TernaryFourierWord ζ t (Matrix.transvection (0 : Fin 3) 1 (1 : K))) (n : ℕ) :
    complexity (gridTensor (fun _ : Fin (n+n) => unitShear K)) ≤
      4 * (t * complexity (gridTensor (fun _ : Fin n => ternarySectorStage ζ))) := by
  let e : (Fin (n+n) → Fin 2) ↪ (Fin n → Fin 2 × Fin 2) :=
    ⟨fun x i => (x (Fin.castAdd n i), x (Fin.natAdd n i)), by
      intro x y h
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · exact congrArg Prod.fst (congrFun h i)
      · exact congrArg Prod.snd (congrFun h i)⟩
  have h := (pairedShear_cost hw n).submatrix e e
  apply (complexity_le_iff ..).mpr
  convert h using 1
  ext x y
  simp only [Matrix.submatrix_apply, gridTensor, Matrix.kroneckerMap_apply, Fin.prod_univ_add,
    Finset.prod_mul_distrib]
  rfl

private theorem complexity_shear_pad (j d : ℕ) :
    complexity (gridTensor (fun _ : Fin j => unitShear K)) ≤
      complexity (gridTensor (fun _ : Fin (j+d) => unitShear K)) := by
  let e : (Fin j → Fin 2) ↪ (Fin (j+d) → Fin 2) :=
    ⟨fun x => Fin.append x (fun _ => 0), fun _ _ h => funext fun i => by
      simpa using congrFun h (Fin.castAdd d i)⟩
  have h := (realizableAtMost_complexity (gridTensor (fun _ : Fin (j+d) => unitShear K))).submatrix e e
  apply (complexity_le_iff ..).mpr
  convert h using 1
  ext x y
  change (∏ i, unitShear K (x i) (y i)) =
    ∏ i, unitShear K (Fin.append x (fun _ : Fin d => 0) i) (Fin.append y (fun _ => 0) i)
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  simp [unitShear]


/-- A fixed ternary word for one unit transvection gives the binary shear bound.
At most one extra bit is needed to partition an odd number of bits into pairs. -/
theorem shearTensorBound_of_ternary_word {ζ : K} {t : ℕ}
    (hw : TernaryFourierWord ζ t (Matrix.transvection (0 : Fin 3) 1 (1 : K)))
    {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hc : ∀ k : ℕ, (complexity (primeTransform 3 k ζ) : ℝ) ≤ C * 3^k * (1 + (k : ℝ))^β) :
    ShearTensorBound K β (8 * t * C) := by
  intro j
  let n := (j+1)/2
  have hj : j ≤ n+n := by dsimp [n]; omega
  have hn : n ≤ j := by dsimp [n]; omega
  have hnn : n+n ≤ j+1 := by dsimp [n]; omega
  have hp := complexity_shear_pad (K := K) j ((n+n)-j)
  rw [Nat.add_sub_of_le hj] at hp
  have hpair : (complexity (gridTensor (fun _ : Fin j => unitShear K)) : ℝ) ≤
      4 * ((t : ℝ) * complexity (gridTensor (fun _ : Fin n => ternarySectorStage ζ))) := by
    exact_mod_cast hp.trans (complexity_shear_paired hw n)
  have hpow : (4 : ℝ)^n ≤ 2 * 2^j := calc
    _ = (2 : ℝ)^(n+n) := by rw [← two_mul, pow_mul]; norm_num
    _ ≤ (2 : ℝ)^(j+1) := pow_le_pow_right₀ (by norm_num) hnn
    _ = _ := by ring
  have hweight : (1 + (n : ℝ)) ^ β ≤ (1 + (j : ℝ)) ^ β :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_left hn 1) hβ
  calc
    _ ≤ 4 * ((t : ℝ) * (C * 4^n * (1 + (n : ℝ))^β)) :=
      hpair.trans (by gcongr; exact ternarySectorStage_bound ζ n hβ hC (fun k _ => hc k))
    _ ≤ 4 * ((t : ℝ) * (C * (2 * 2^j) * (1 + (j : ℝ))^β)) := by gcongr
    _ = _ := by ring

end

end FiniteFourier
end LinearAlgebra
end OAI
