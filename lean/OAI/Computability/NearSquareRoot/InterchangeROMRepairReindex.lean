import OAI.Computability.NearSquareRoot.InterchangeROMRepairLowerSizes

/-! # One-dimensional serial row and check indices -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair

open Matrix

variable {R I J I' J' : Type} {m : ℕ} [CommRing R]
  [Fintype I] [DecidableEq I] [Fintype J] [Fintype I'] [DecidableEq I'] [Fintype J']

def Spec.reindex (t : Spec R I J m) (a : I' ≃ I) (b : J' ≃ J) : Spec R I' J' m where
  base := t.base.submatrix a a
  term j := (t.term j).submatrix a a
  extract := t.extract.submatrix b a
  restore := t.restore.submatrix a b
  correct η o i := (t.correct η o i).submatrix b b

omit [Fintype I] [DecidableEq I] [Fintype J] [Fintype I'] [DecidableEq I'] [Fintype J'] in
private theorem onSign_reindex (t : Spec R I J m) (a : I' ≃ I) (b : J' ≃ J) (η : Fin m → Bool) :
    onSign (t.reindex a b) η = (onSign t η).submatrix a a := by
  ext i j
  simp [onSign, Spec.reindex, Matrix.sum_apply]

private theorem sm_pow (P : Matrix I I R) (a : I' ≃ I) (n : ℕ) :
    P.submatrix a a ^ n = (P^n).submatrix a a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,ih,submatrix_mul_equiv,pow_succ]

private theorem sm_add {A B D E : Type} (P Q : Matrix D E R) (a : A → D) (b : B → E) :
    P.submatrix a b + Q.submatrix a b = (P+Q).submatrix a b := rfl

private theorem sm_sub {A B D E : Type} (P Q : Matrix D E R) (a : A → D) (b : B → E) :
    P.submatrix a b - Q.submatrix a b = (P-Q).submatrix a b := rfl

private theorem sm_scale {A B D E : Type} (s : R) (P : Matrix D E R) (a : A → D) (b : B → E) :
    s • P.submatrix a b = (s • P).submatrix a b := rfl

theorem response_reindex (t : Spec R I J m) (a : I' ≃ I) (b : J' ≃ J)
    (η : Fin m → Bool) (order : ℕ) (half : R) :
    response (t.reindex a b) η order half = (response t η order half).submatrix a a := by
  simp only [response, onSign_reindex, sm_pow]
  simp only [Spec.reindex, submatrix_mul_equiv, sm_add, sm_sub, sm_scale]

theorem accepts_reindex [DecidableEq R] (t : Spec R I J m) (a : I' ≃ I) (b : J' ≃ J)
    (order : ℕ) (half : R) (h : accepts t order half = true) :
    accepts (t.reindex a b) order half = true := by
  rw [accepts_iff] at h ⊢
  intro η
  rw [response_reindex,h,← sm_scale,submatrix_one_equiv]

/-- A family of valid ROMs on contiguous row indices with computable integer dimensions. -/
theorem exists_fin_accepted {K : Type} [Field K] [DecidableEq K] {m : ℕ} (hm : 2 ≤ m)
    (half : K) (hh : 2 * half = 1) :
    ∃ t : Spec K (Fin (Sizes.rows m * Sizes.basisCount m))
        (Fin (Sizes.checkRows m * Sizes.basisCount m)) m,
      accepts t (Sizes.pencilOrder m) half = true := by
  obtain ⟨t,ht⟩ := Sizes.exists_accepted hm half hh
  exact ⟨_, accepts_reindex t finProdFinEquiv.symm finProdFinEquiv.symm _ _ ht⟩

end InterchangeROMRepair

end NearSquareRoot
end Computability
end OAI
