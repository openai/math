import OAI.LinearAlgebra.SpectralBooks.MaskDiagonal
import OAI.LinearAlgebra.SpectralBooks.NatSpectralExponent
import OAI.LinearAlgebra.SpectralBooks.RawLogPrice

/-! # Prices of partial diagonals on a fixed set of sites

The same spectral point evaluates all the partial diagonals. Their positive
label dimensions form a monotone multiplicative family, so its entire
logarithmic price law is determined by the binary label.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SiteTensor

open scoped Classical NNReal

variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

/-- A partial diagonal coefficient tests consistency with any specified occupied site. -/
theorem Raw.maskDiagonal_coeff_at (S : Finset I) {i₀ : I} (hi₀ : i₀ ∈ S)
    {α : Type} [Fintype α] (x : ∀ i, MaskLeg S α i) :
    (Raw.maskDiagonal K S α).coeff x = if ∀ (i : I) (hi : i ∈ S), x i hi = x i₀ hi₀ then 1 else 0 := by
  unfold Raw.maskDiagonal Crossing.basisTensor
  dsimp only
  rw [Finset.sum_eq_single (x i₀ hi₀)]
  · simp only [funext_iff]
  · intro a _ hne
    exact ite_eq_right fun ha ↦ hne (congrFun (congrFun ha i₀) hi₀).symm
  · simp

omit [DecidableEq I] in
/-- Selecting one input coefficient at each output basis index is a local restriction. -/
theorem Raw.restrict_by_read {X Y : Raw.{0} I K} (g : ∀ i, X.Leg i → Y.Leg i)
    (hcoeff : ∀ x, X.coeff x = Y.coeff (fun i ↦ g i (x i))) : X.Restricts Y := by
  classical
  refine ⟨fun i x y ↦ if y = g i x then 1 else 0, fun x ↦ ?_⟩
  rw [hcoeff x]
  simp_rw [Fintype.prod_boole]
  have heq (y : ∀ i, Y.Leg i) : (∀ i, y i = g i (x i)) ↔ y = fun i ↦ g i (x i) :=
    funext_iff.symm
  simp [heq, mul_ite]

/-- Projecting the labels at all occupied sites realizes embeddings of label sets. -/
theorem Raw.maskDiagonal_restricts_of_embedding (S : Finset I) (hS : S.Nonempty)
    {α β : Type} [Fintype α] [Fintype β] (e : α ↪ β) :
    (Raw.maskDiagonal K S α).Restricts (Raw.maskDiagonal K S β) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hS
  let g (i : I) (x : MaskLeg S α i) : MaskLeg S β i := fun hi ↦ e (x hi)
  apply Raw.restrict_by_read (X := Raw.maskDiagonal K S α) (Y := Raw.maskDiagonal K S β) g
  intro x
  calc
    _ = _ := Raw.maskDiagonal_coeff_at (K := K) S hi₀ x
    _ = _ := ?_
    _ = _ := (Raw.maskDiagonal_coeff_at (K := K) S hi₀ (fun i ↦ g i (x i))).symm
  simp [g]


theorem ofRaw_maskDiagonal_equiv (S : Finset I) (hS : S.Nonempty)
    {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) :
    ofRaw (Raw.maskDiagonal K S α) = ofRaw (Raw.maskDiagonal K S β) :=
  ofRaw_eq_iff.mpr ⟨Raw.maskDiagonal_restricts_of_embedding S hS e.toEmbedding,
    Raw.maskDiagonal_restricts_of_embedding S hS e.symm.toEmbedding⟩

omit [DecidableEq I] in
/-- Multiplicativity in the dimension, using independent pairs of labels. -/
theorem ofRaw_maskDiagonal_prod (S : Finset I) (α β : Type) [Fintype α] [Fintype β] :
    ofRaw (Raw.maskDiagonal K S (α × β)) =
      ofRaw (Raw.maskDiagonal K S α) * ofRaw (Raw.maskDiagonal K S β) := by
  let a (x : α) (i : I) (_ : i ∈ S) := x
  let b (x : β) (i : I) (_ : i ∈ S) := x
  let c (x : α × β) (i : I) (_ : i ∈ S) := x
  let e (i : I) : MaskLeg S (α × β) i ≃ MaskLeg S α i × MaskLeg S β i :=
    { toFun := fun f ↦ (fun j ↦ (f j).1, fun j ↦ (f j).2)
      invFun := fun f j ↦ (f.1 j, f.2 j)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let : ∀ i, Fintype (MaskLeg S α i) := (Raw.maskDiagonal K S α).finiteLeg
  let : ∀ i, Fintype (MaskLeg S β i) := (Raw.maskDiagonal K S β).finiteLeg
  let : ∀ i, Fintype (MaskLeg S (α × β) i) := (Raw.maskDiagonal K S (α × β)).finiteLeg
  exact basisTensor_paired_eq_mul (K := K) (A := MaskLeg S α) (B := MaskLeg S β)
    (C := MaskLeg S (α × β)) a b c e (fun _ _ _ ↦ rfl)

variable [Nonempty I]

/-- The natural label dimensions as a monoid homomorphism into tensor classes. -/
def maskDiagonalHom (K : Type*) [Field K] (S : Finset I) (hS : S.Nonempty) :
    ℕ →* TensorClass.{0} I K where
  toFun n := ofRaw (Raw.maskDiagonal K S (Fin n))
  map_one' := by
    obtain ⟨i, hi⟩ := hS
    apply ofRaw_eq_iff.mpr
    apply Raw.reindex_equivalent (X := Raw.maskDiagonal K S (Fin 1)) (Y := Raw.one I K)
      (fun j ↦ Equiv.ofUnique (MaskLeg S (Fin 1) j) PUnit)
    intro x
    calc
      _ = _ := Raw.maskDiagonal_coeff_at (K := K) S hi x
      _ = _ := ite_eq_left (fun _ _ ↦ Subsingleton.elim (α := Fin 1) _ _)
  map_mul' n m := (ofRaw_maskDiagonal_equiv S hS finProdFinEquiv.symm).trans
    (ofRaw_maskDiagonal_prod S (Fin n) (Fin m))

/-- Increasing dimension gives a restriction comparison inside the fixed ambient format. -/
theorem maskDiagonalHom_mono (S : Finset I) (hS : S.Nonempty) : Monotone (maskDiagonalHom K S hS) :=
  fun _ _ h ↦ Raw.maskDiagonal_restricts_of_embedding S hS (Fin.castLEEmb h)

/-- Exact base-two price of a common label on a nonempty support. -/
theorem maskDiagonal_log_price
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
    (S : Finset I) (hS : S.Nonempty) {q : ℕ} (hq : 0 < q) :
    Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K S (Fin q))) : ℝ) =
      Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K S (Fin 2))) : ℝ) * Real.logb 2 q := by
  let v := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (maskDiagonalHom K S hS)
  apply spectral_natCast_logb (A := ℕ) (v := v) _ q hq
  intro a b _ hab
  exact φ.property.2.2.2.2 _ _ (maskDiagonalHom_mono S hS hab)

omit [Nonempty I] in
/-- A partial diagonal on a nonempty support with at least one label is nonzero. -/
theorem Raw.maskDiagonal_ne_zero (S : Finset I) (hS : S.Nonempty)
    (α : Type) [Fintype α] [Nonempty α] : (Raw.maskDiagonal K S α).coeff ≠ 0 := by
  obtain ⟨i, hi⟩ := hS
  let a : α := Classical.choice inferInstance
  intro hzero
  have h := congrFun hzero (fun _ _ ↦ a)
  change (Raw.maskDiagonal K S α).coeff (fun _ _ ↦ a) = 0 at h
  exact one_ne_zero (by simpa only [Raw.maskDiagonal_coeff_at (K := K) S hi (fun _ _ ↦ a),
    implies_true, ite_true] using h)

omit [Nonempty I] in
/-- Deleting occurrences of the common label is a local restriction. -/
theorem Raw.maskDiagonal_restricts_of_subset {S T : Finset I} (h : S ⊆ T)
    (α : Type) [Fintype α] :
    (Raw.maskDiagonal K S α).Restricts (Raw.maskDiagonal K T α) := by
  let c (a : α) (i : I) (_ : i ∈ T) := a
  let : ∀ i, Fintype (MaskLeg T α i) := (Raw.maskDiagonal K T α).finiteLeg
  apply (Crossing.restriction_basisTensor_iff (F := K) (A := MaskLeg T α) (B := MaskLeg S α)
    c (Raw.maskDiagonal K S α).coeff).mpr
  refine ⟨fun i x y ↦ if x = (fun hi ↦ y (h hi)) then 1 else 0, fun x ↦ ?_⟩
  simp only [Raw.maskDiagonal, Crossing.basisTensor, Fintype.prod_boole, c, funext_iff]

/-- One site's diagonal is the tensor class of the scalar unit. -/
theorem ofRaw_maskDiagonal_singleton (i : I) (α : Type) [Fintype α] [Nonempty α] :
    ofRaw (Raw.maskDiagonal K {i} α) = 1 := by
  apply ofRaw_eq_iff.mpr
  refine ⟨Raw.restrict_by_read (Y := Raw.one I K) (fun _ _ ↦ PUnit.unit) ?_,
    Raw.one_restricts_of_nonzero _ (Raw.maskDiagonal_ne_zero _ (Finset.singleton_nonempty i) α)⟩
  intro x
  calc
    _ = _ := Raw.maskDiagonal_coeff_at (K := K) {i} (Finset.mem_singleton_self i) x
    _ = _ := ite_eq_left (fun j hj ↦ by obtain rfl := Finset.mem_singleton.mp hj; rfl)

omit [Nonempty I] in
/-- Equating the common labels where two nonempty diagonals overlap supplies
the diagonal on their union. -/
theorem Raw.maskDiagonal_union_restricts_mul (A B : Finset I) (hI : (A ∩ B).Nonempty)
    (α : Type) [Fintype α] :
    (Raw.maskDiagonal K (A ∪ B) α).Restricts
      ((Raw.maskDiagonal K A α).mul (Raw.maskDiagonal K B α)) := by
  obtain ⟨i₀, hi₀⟩ := hI
  obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hi₀
  let g₁ (i : I) (x : MaskLeg (A ∪ B) α i) (hi : i ∈ A) := x (Finset.mem_union_left _ hi)
  let g₂ (i : I) (x : MaskLeg (A ∪ B) α i) (hi : i ∈ B) := x (Finset.mem_union_right _ hi)
  apply Raw.restrict_by_read (fun i x ↦ (g₁ i x, g₂ i x))
  intro x
  change (maskDiagonal K (A ∪ B) α).coeff x =
    (maskDiagonal K A α).coeff (fun i ↦ g₁ i (x i)) *
      (maskDiagonal K B α).coeff (fun i ↦ g₂ i (x i))
  rw [Raw.maskDiagonal_coeff_at (K := K) (A ∪ B) (Finset.mem_union_left _ ha) x,
    Raw.maskDiagonal_coeff_at (K := K) A ha (fun i ↦ g₁ i (x i)),
    Raw.maskDiagonal_coeff_at (K := K) B hb (fun i ↦ g₂ i (x i))]
  let v := x i₀ (Finset.mem_union_left B ha)
  have heq : (∀ (i : I) (hi : i ∈ A ∪ B), x i hi = v) ↔
      (∀ (i : I) (hi : i ∈ A), g₁ i (x i) hi = v) ∧
      ∀ (i : I) (hi : i ∈ B), g₂ i (x i) hi = v := by
    constructor
    · intro H
      exact ⟨fun _ _ ↦ H _ _, fun _ _ ↦ H _ _⟩
    · rintro ⟨H₁, H₂⟩ i hi
      rcases Finset.mem_union.mp hi with h | h
      · exact H₁ i h
      · exact H₂ i h
  change (if ∀ (i : I) (hi : i ∈ A ∪ B), x i hi = v then (1 : K) else 0) =
    (if ∀ (i : I) (hi : i ∈ A), g₁ i (x i) hi = v then 1 else 0) *
      (if ∀ (i : I) (hi : i ∈ B), g₂ i (x i) hi = v then 1 else 0)
  split_ifs <;> simp_all

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))

/-- The common binary label price at the chosen sites, evaluated at a single
ambient spectral point and scale. -/
def maskDiagonalPrice (c : ℝ) (S : Finset I) : ℝ := rawLogPrice φ c (Raw.maskDiagonal K S (Fin 2))

theorem rawLogPrice_maskDiagonal (c : ℝ) (S : Finset I) (hS : S.Nonempty) {q : ℕ} (hq : 0 < q) :
    rawLogPrice φ c (Raw.maskDiagonal K S (Fin q)) = maskDiagonalPrice φ c S * Real.logb 2 q := by
  unfold maskDiagonalPrice rawLogPrice
  rw [maskDiagonal_log_price φ S hS hq, mul_assoc]

theorem maskDiagonalPrice_mono {c : ℝ} (hc : 0 ≤ c) : Monotone (maskDiagonalPrice φ c) :=
  fun _ _ h ↦ rawLogPrice_mono φ hc (Raw.maskDiagonal_restricts_of_subset h (Fin 2))

omit [DecidableEq I] in
theorem maskDiagonalPrice_nonneg {c : ℝ} (hc : 0 ≤ c) (S : Finset I) :
    0 ≤ maskDiagonalPrice φ c S := rawLogPrice_nonneg φ hc _

theorem maskDiagonalPrice_singleton (c : ℝ) (i : I) : maskDiagonalPrice φ c {i} = 0 := by
  simp [maskDiagonalPrice, rawLogPrice, ofRaw_maskDiagonal_singleton, φ.property.2.1]

/-- Sending the independent labels on overlapping sets can supply one common
label on their union. -/
theorem maskDiagonalPrice_union_le {c : ℝ} (hc : 0 ≤ c) (A B : Finset I) (hAB : (A ∩ B).Nonempty) :
    maskDiagonalPrice φ c (A ∪ B) ≤ maskDiagonalPrice φ c A + maskDiagonalPrice φ c B := by
  have hm := rawLogPrice_mono φ hc (Raw.maskDiagonal_union_restricts_mul A B hAB (Fin 2))
  rwa [rawLogPrice_mul φ c _ _
    (Raw.maskDiagonal_ne_zero A (hAB.mono Finset.inter_subset_left) (Fin 2))
    (Raw.maskDiagonal_ne_zero B (hAB.mono Finset.inter_subset_right) (Fin 2))] at hm

/-- A wire from any occupied site suffices to append a common label at another site. -/
theorem maskDiagonalPrice_insert_le_wire {c : ℝ} (hc : 0 ≤ c) (A : Finset I) {x : I}
    (hx : x ∈ A) (z : I) :
    maskDiagonalPrice φ c (insert z A) ≤ maskDiagonalPrice φ c A + maskDiagonalPrice φ c {x, z} := by
  have hunion : A ∪ {x,z} = insert z A := by ext w; simp; grind
  rw [← hunion]
  apply maskDiagonalPrice_union_le φ hc
  exact ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_insert_self _ _⟩⟩

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
