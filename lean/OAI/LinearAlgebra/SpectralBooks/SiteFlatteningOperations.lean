import OAI.LinearAlgebra.SpectralBooks.SiteFlattening
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.SumDef
import OAI.LinearAlgebra.SpectralBooks.BlockDiagRank

/-! # Additivity of bipartite flattening rank

Rows and columns of a tensor direct sum have tags at each site. Across a proper
cut the two homogeneous tags on each side select a block diagonal submatrix.
All remaining rows and columns vanish.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

noncomputable section

section

/-- Deleting all-zero rows and columns preserves the rank. -/
private theorem rank_eq_rank_on_support {K R C R' C' : Type*} [Field K]
    [Fintype R'] [Fintype C'] [Fintype C] (M : Matrix R C K)
    (r : R' ↪ R) (c : C' ↪ C)
    (hr : ∀ x ∉ Set.range r, ∀ y, M x y = 0)
    (hc : ∀ y ∉ Set.range c, ∀ x, M x y = 0) :
    M.rank = (M.submatrix r c).rank := by
  classical
  let P : Matrix R R' K := fun i a => if i = r a then 1 else 0
  let Q : Matrix C' C K := fun b j => if c b = j then 1 else 0
  have left (x : R) (b : C') : (P * M.submatrix r c) x b = M x (c b) := by
    rw [Matrix.mul_apply]
    by_cases hx : x ∈ Set.range r
    · obtain ⟨a, rfl⟩ := hx
      simp [P, Matrix.submatrix, r.injective.eq_iff, ite_mul]
    · have h (a : R') : x ≠ r a := fun e => hx ⟨a, e.symm⟩
      simp [P, h, hr _ hx]
  have eq : M = P * M.submatrix r c * Q := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [left]
    by_cases hy : y ∈ Set.range c
    · obtain ⟨b, rfl⟩ := hy
      simp [Q, c.injective.eq_iff, mul_ite]
    · have h (b : C') : c b ≠ y := fun e => hy ⟨b, e⟩
      simp [Q, h, hc _ hy]
  exact le_antisymm (calc
    M.rank = (P * M.submatrix r c * Q).rank := congrArg Matrix.rank eq
    _ ≤ (P * M.submatrix r c).rank := Matrix.rank_mul_le_left _ _
    _ ≤ _ := Matrix.rank_mul_le_right _ _) (Matrix.rank_submatrix_le M r c)

namespace SiteTensor

/-- Include the two homogeneous tag assignments in all assignments on one side. -/
private def homogeneousTags {J : Type*} [Nonempty J] (A B : J → Type*) :
    ((∀ j, A j) ⊕ (∀ j, B j)) ↪ (∀ j, A j ⊕ B j) where
  toFun := Sum.elim (fun a j => Sum.inl (a j)) (fun b j => Sum.inr (b j))
  inj' := by
    rintro (x|x) (y|y) h
    · exact congrArg Sum.inl (funext fun j => Sum.inl.inj (congrFun h j))
    · cases congrFun h (Classical.arbitrary J)
    · cases congrFun h (Classical.arbitrary J)
    · exact congrArg Sum.inr (funext fun j => Sum.inr.inj (congrFun h j))

@[simp] private theorem homogeneousTags_inl {J : Type*} [Nonempty J] (A B : J → Type*)
    (a : ∀ j, A j) (j : J) : homogeneousTags A B (Sum.inl a) j = Sum.inl (a j) := rfl

@[simp] private theorem homogeneousTags_inr {J : Type*} [Nonempty J] (A B : J → Type*)
    (b : ∀ j, B j) (j : J) : homogeneousTags A B (Sum.inr b) j = Sum.inr (b j) := rfl

variable {I K : Type*} {A B : I → Type*}
variable (s : I → Prop) [DecidablePred s] [Fintype I] [Field K]
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

open Crossing

/-- Across a cut with sites on each side the two summands give independent
diagonal blocks. -/
theorem cutMatrix_rank_sumCoeff [Nonempty {i // s i}] [Nonempty {i // ¬ s i}]
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    (cutMatrix s (sumCoeff T U)).rank = (cutMatrix s T).rank + (cutMatrix s U).rank := by
  classical
  let : Nonempty I := ⟨(Classical.arbitrary {i // s i}).val⟩
  let r := homogeneousTags (fun i : {i // s i} => A i) (fun i => B i)
  let c := homogeneousTags (fun i : {i // ¬ s i} => A i) (fun i => B i)
  let M := cutMatrix s (sumCoeff T U)
  have support (x y) (h : x ∉ Set.range r ∨ y ∉ Set.range c) : M x y = 0 := by
    apply sumCoeff_mixed
    · intro a he
      have e := (cutEquiv s (fun i => A i ⊕ B i)).apply_symm_apply (x,y)
      rw [← he] at e
      exact h.elim (fun hx => hx ⟨Sum.inl (fun i => a i), congrArg Prod.fst e⟩)
        (fun hy => hy ⟨Sum.inl (fun i => a i), congrArg Prod.snd e⟩)
    · intro b he
      have e := (cutEquiv s (fun i => A i ⊕ B i)).apply_symm_apply (x,y)
      rw [← he] at e
      exact h.elim (fun hx => hx ⟨Sum.inr (fun i => b i), congrArg Prod.fst e⟩)
        (fun hy => hy ⟨Sum.inr (fun i => b i), congrArg Prod.snd e⟩)
  have block : M.submatrix r c = Matrix.fromBlocks (cutMatrix s T) 0 0 (cutMatrix s U) := by
    ext x y
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        change sumCoeff T U _ = T _
        convert sumCoeff_inl T U ((cutEquiv s A).symm (x,y)) using 1
        congr 1
        funext i
        by_cases hi : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
          r, c, hi]
      | inr y =>
        apply sumCoeff_mixed
        · intro a he
          have h := congrFun he (Classical.arbitrary {i // ¬ s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // ¬ s i}).property] at h
        · intro b he
          have h := congrFun he (Classical.arbitrary {i // s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // s i}).property] at h
    | inr x =>
      cases y with
      | inl y =>
        apply sumCoeff_mixed
        · intro a he
          have h := congrFun he (Classical.arbitrary {i // s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // s i}).property] at h
        · intro b he
          have h := congrFun he (Classical.arbitrary {i // ¬ s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // ¬ s i}).property] at h
      | inr y =>
        change sumCoeff T U _ = U _
        convert sumCoeff_inr T U ((cutEquiv s B).symm (x,y)) using 1
        congr 1
        funext i
        by_cases hi : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
          r, c, hi]
  change M.rank = _
  rw [rank_eq_rank_on_support M r c (fun x hx y => support x y (Or.inl hx))
    (fun y hy x => support x y (Or.inr hy)), block, rank_fromBlocks_diagonal]

namespace Raw

universe v

/-- The zero tensor gives the zero matrix across every cut. -/
theorem cutMatrix_rank_zero (F : Type*) [Field F] :
    (cutMatrix s (zero.{v} I F).coeff).rank = 0 :=
  Matrix.rank_zero

/-- Each side of the scalar unit has just one coordinate tuple. -/
theorem cutMatrix_rank_one (F : Type*) [Field F] :
    (cutMatrix s (one.{v} I F).coeff).rank = 1 := by
  classical
  let r : ({i // s i} → PUnit.{v+1}) ≃ Unit := Equiv.ofUnique _ _
  let c : ({i // ¬s i} → PUnit.{v+1}) ≃ Unit := Equiv.ofUnique _ _
  have eq : cutMatrix s (one.{v} I F).coeff = (1 : Matrix Unit Unit F).submatrix r c := by
    ext x y
    change 1 = (1 : Matrix Unit Unit F) (r x) (c y)
    simp
  rw [eq]
  exact (Matrix.rank_submatrix (1 : Matrix Unit Unit F) r c).trans
    ((Matrix.rank_one (R := F)).trans Fintype.card_unit)

end Raw

end SiteTensor

end

end

end SpectralBooks
end LinearAlgebra
end OAI
