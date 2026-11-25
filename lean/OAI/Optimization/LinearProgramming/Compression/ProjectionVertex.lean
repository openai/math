import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-! # Vertices of finite systems of inequalities

Adding the signed coordinate rows of a closed orthant makes the normals of a
finite system separate directions. A point with as few slack inequalities as
possible then has enough tight normals to determine its coordinates uniquely. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

variable {K : Type*}

open Finset

variable {K E ι : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E] [Fintype ι]

private theorem moveToTightRow (A : ι → E →ₗ[K] K) (b : ι → K) (x d : E)
    (hx : ∀ i, A i x ≤ b i) (hd : ∀ i, A i x = b i → A i d = 0)
    (hpos : ∃ i, 0 < A i d) :
    ∃ y, (∀ i, A i y ≤ b i) ∧ (∀ i, A i x = b i → A i y = b i) ∧
      ∃ k, A k x < b k ∧ A k y = b k := by
  classical
  let s := univ.filter fun i => 0 < A i d
  obtain ⟨i, hi⟩ := hpos
  have hs : s.Nonempty := ⟨i, by simpa [s] using hi⟩
  let ratio := fun i => (b i - A i x) / A i d
  obtain ⟨k, hk, hmin⟩ := s.exists_min_image ratio hs
  have hkpos : 0 < A k d := by simpa [s] using hk
  have hnonneg : 0 ≤ ratio k := div_nonneg (sub_nonneg.mpr (hx k)) hkpos.le
  have hhit : ratio k * A k d = b k - A k x := div_mul_cancel₀ _ hkpos.ne'
  refine ⟨x + ratio k • d, ?_, ?_, k, ?_, ?_⟩
  · intro j
    simp only [map_add, map_smul, smul_eq_mul]
    by_cases hj : 0 < A j d
    · have hle : ratio k * A j d ≤ b j - A j x :=
        (le_div_iff₀ hj).mp (hmin j (by simpa [s] using hj))
      linarith
    · exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hnonneg (le_of_not_gt hj))).trans (hx j)
  · intro j hj
    simp [hd j hj, hj]
  · exact lt_of_le_of_ne (hx k) fun he => hkpos.ne' (hd k he)
  · simp only [map_add, map_smul, smul_eq_mul, hhit, add_sub_cancel]

/-- A nonempty pointed finite inequality system has a feasible point whose
active rows separate directions. The separating hypothesis holds after adding
the signed coordinate inequalities for any orthant. -/
theorem exists_feasible_tight_rows_separate (A : ι → E →ₗ[K] K) (b : ι → K)
    (hsep : ∀ d : E, (∀ i, A i d = 0) → d = 0)
    (hne : ∃ x, ∀ i, A i x ≤ b i) :
    ∃ x, (∀ i, A i x ≤ b i) ∧
      ∀ d : E, (∀ i, A i x = b i → A i d = 0) → d = 0 := by
  classical
  let slack := fun x : E => univ.filter fun i => A i x < b i
  let p := fun n : ℕ => ∃ x, (∀ i, A i x ≤ b i) ∧ (slack x).card = n
  obtain ⟨x₀, hx₀⟩ := hne
  have hex : ∃ n, p n := ⟨_, x₀, hx₀, rfl⟩
  obtain ⟨x, hx, hcard⟩ := Nat.find_spec hex
  refine ⟨x, hx, fun d hd => ?_⟩
  by_contra hne'
  obtain ⟨j, hj⟩ : ∃ i, A i d ≠ 0 := by
    by_contra! h
    exact hne' (hsep d h)
  have hmove : ∃ y, (∀ i, A i y ≤ b i) ∧ (∀ i, A i x = b i → A i y = b i) ∧
      ∃ k, A k x < b k ∧ A k y = b k := by
    rcases lt_or_gt_of_ne hj with hneg | hpos
    · apply moveToTightRow A b x (-d) hx
      · intro i hi
        simp [hd i hi]
      · exact ⟨j, by simpa using hneg⟩
    · exact moveToTightRow A b x d hx hd ⟨j, hpos⟩
  obtain ⟨y, hy, hpres, k, hk, hky⟩ := hmove
  have hlt : slack y ⊂ slack x := by
    refine Finset.ssubset_iff_exists_subset_erase.mpr ⟨k, by simpa [slack] using hk, ?_⟩
    intro i hi
    have hyi : A i y < b i := by simpa [slack] using hi
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · rintro rfl
      exact hyi.ne hky
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, lt_of_le_of_ne (hx i) fun he => hyi.ne (hpres i he)⟩
  have hsmall := Finset.card_lt_card hlt
  rw [hcard] at hsmall
  exact (Nat.find_min hex hsmall) ⟨y, hy, rfl⟩

/-- At some feasible point the tight normals span the whole dual space. -/
theorem exists_feasible_tight_rows_span (A : ι → E →ₗ[K] K) (b : ι → K)
    (hsep : ∀ d : E, (∀ i, A i d = 0) → d = 0)
    (hne : ∃ x, ∀ i, A i x ≤ b i) :
    ∃ x, (∀ i, A i x ≤ b i) ∧
      Submodule.span K (Set.range (fun i : {i // A i x = b i} => A i)) = ⊤ := by
  obtain ⟨x, hx, hker⟩ := exists_feasible_tight_rows_separate A b hsep hne
  refine ⟨x, hx, eq_top_iff.mpr fun f _ => mem_span_of_iInf_ker_le_ker ?_⟩
  intro d hd
  have h := hker d fun i hi => ((Submodule.mem_iInf _).mp hd ⟨i, hi⟩ : A i d = 0)
  simp [h]

open scoped Matrix

/-- An explicit square nonsingular subsystem of tight equalities at a feasible
vertex. The cardinality of the original row set does not enter the size of
this subsystem. -/
theorem exists_feasible_tight_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (b : ι → K)
    (hsep : ∀ d : κ → K, A *ᵥ d = 0 → d = 0) (hne : ∃ x, A *ᵥ x ≤ b) :
    ∃ x, A *ᵥ x ≤ b ∧ ∃ sel : κ → ι, Function.Injective sel ∧
      (A.submatrix sel id).det ≠ 0 ∧ ∀ j, (A *ᵥ x) (sel j) = b (sel j) := by
  classical
  let row (i : ι) : (κ → K) →ₗ[K] K := (LinearMap.proj (R := K) i).comp A.mulVecLin
  have hrow : ∀ d, (∀ i, row i d = 0) → d = 0 := fun d hd => hsep d (funext hd)
  obtain ⟨x, hx, hspan⟩ := exists_feasible_tight_rows_span row b hrow hne
  let tight := {i // row i x = b i}
  obtain ⟨σ, pick, hp, hs, hli⟩ := exists_linearIndependent' K (fun i : tight => row i)
  let forms : σ → (κ → K) →ₗ[K] K := (fun i : tight => row i) ∘ pick
  have hfull : Submodule.span K (Set.range forms) = ⊤ := hs.trans hspan
  let := Finite.of_injective pick hp
  let := Fintype.ofFinite σ
  let B : Module.Basis σ K ((κ → K) →ₗ[K] K) := Module.Basis.mk hli hfull.ge
  let e : κ ≃ σ := Fintype.equivOfCardEq <|
    (Module.finrank_eq_card_basis (Pi.basisFun K κ).dualBasis).symm.trans
      (Module.finrank_eq_card_basis B)
  let sel := fun j : κ => (pick (e j)).val
  refine ⟨x, hx, sel, Subtype.val_injective.comp (hp.comp e.injective), ?_,
    fun j => (pick (e j)).property⟩
  apply IsUnit.ne_zero
  apply (A.submatrix sel id).isUnit_iff_isUnit_det.mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  apply sub_eq_zero.mp
  apply hrow
  intro i
  have hz (j : σ) : forms j (u - v) = 0 := by
    rw [map_sub, sub_eq_zero]
    have h := congrFun huv (e.symm j)
    change row (sel (e.symm j)) u = row (sel (e.symm j)) v at h
    simpa [forms, sel] using h
  have hm : row i ∈ Submodule.span K (Set.range forms) := by simp [hfull]
  apply Submodule.span_induction (p := fun f _ => f (u - v) = 0) _ _ _ _ hm
  · rintro _ ⟨j, rfl⟩
    exact hz j
  · simp
  · intro _ _ _ _ h₁ h₂
    simp [h₁, h₂]
  · intro _ _ _ h
    simp [h]

/-- Append one signed coordinate row per column. A true sign adds the row
`-xⱼ ≤ 0`, and a false sign adds `xⱼ ≤ 0`. -/
def orthantCutRows {κ : Type*} [DecidableEq κ] (A : Matrix ι κ K) (positive : κ → Bool) :
    Matrix (ι ⊕ κ) κ K :=
  Matrix.of fun i j => i.elim (fun r => A r j)
    (fun k => if j = k then (if positive k then -1 else 1) else 0)

omit [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι] in
@[simp] theorem orthantCutRows_mulVec_inl {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (positive : κ → Bool) (x : κ → K) (i : ι) :
    (orthantCutRows A positive *ᵥ x) (.inl i) = (A *ᵥ x) i := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι] in
@[simp] theorem orthantCutRows_mulVec_inr {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (positive : κ → Bool) (x : κ → K) (j : κ) :
    (orthantCutRows A positive *ᵥ x) (.inr j) = if positive j then -x j else x j := by
  simp [orthantCutRows, Matrix.mulVec, dotProduct, ite_mul]

/-- Every feasible system has a feasible point uniquely specified by as many
independent original or signed-coordinate equalities as there are variables.
The choice of orthant only changes row signs; its new right-hand sides are zero. -/
theorem exists_orthant_tight_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (b : ι → K) (hne : ∃ x, A *ᵥ x ≤ b) :
    ∃ (positive : κ → Bool) (x : κ → K), A *ᵥ x ≤ b ∧
      ∃ sel : κ → ι ⊕ κ, Function.Injective sel ∧
        ((orthantCutRows A positive).submatrix sel id).det ≠ 0 ∧
        ∀ j, (orthantCutRows A positive *ᵥ x) (sel j) = (sel j).elim b (fun _ => 0) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  let positive := fun j => decide (0 ≤ x₀ j)
  let cut := orthantCutRows A positive
  let rhs : ι ⊕ κ → K := Sum.elim b (fun _ => 0)
  have hfeas : cut *ᵥ x₀ ≤ rhs := by
    intro i
    cases i with
    | inl i => exact hx₀ i
    | inr j =>
      by_cases hj : 0 ≤ x₀ j
      · simp [cut, rhs, positive, hj]
      · simpa [cut, rhs, positive, hj] using (le_of_not_ge hj)
  have hsep (d : κ → K) (hd : cut *ᵥ d = 0) : d = 0 := by
    funext j
    have h := congrFun hd (.inr j)
    cases hj : positive j <;> simpa [cut, hj] using h
  obtain ⟨x, hx, sel, hs, hdet, ht⟩ := exists_feasible_tight_submatrix cut rhs hsep ⟨_, hfeas⟩
  exact ⟨positive, x, fun i => hx (.inl i), sel, hs, hdet, ht⟩

end Compression
end LinearProgramming
end Optimization
end OAI
