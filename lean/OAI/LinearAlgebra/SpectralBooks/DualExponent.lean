import OAI.LinearAlgebra.SpectralBooks.ArithmeticExponent
import OAI.LinearAlgebra.SpectralBooks.Elongated

/-! # The dual exponent of formal arithmetic matrix multiplication -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

/-- The supremum of `t ∈ [0, 1]` such that the formal arithmetic exponent of
the rectangular weights `(1,1,t)` is two. -/
noncomputable def formalAlpha (F : Type*) [Field F] : ℝ := dualExponent (formalOmega F 1 1)

theorem formalOmega_one_one_zero (F : Type*) [Field F] : formalOmega F 1 1 0 = 2 := by
  let S := {τ : ℝ | FormalAdmissibleExponent F 1 1 0 τ}
  have h0 : (0 : ℝ) ≤ 0 := le_rfl
  have h1 : (0 : ℝ) ≤ 1 := zero_le_one
  have hmem := formalAdmissibleExponent_naive F h1 h1 h0
  norm_num at hmem
  have hbound : ∀ τ ∈ S, (2 : ℝ) ≤ τ := by
    intro τ hτ
    have h := FormalAdmissibleExponent.load_le (F := F) (w12 := 1) (w23 := 1) (w31 := 0) hτ 1
    norm_num [loads] at h
    exact h
  exact le_antisymm (csInf_le (s := S) ⟨2, hbound⟩ hmem) (le_csInf ⟨2, hmem⟩ hbound)

/-- The exponent-two rectangular weights contain zero. An upper bound for
each admissible weight therefore bounds their supremum. -/
theorem formalAlpha_le {F : Type*} [Field F] {b : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, formalOmega F 1 1 t = 2 → t ≤ b) :
    formalAlpha F ≤ b := by
  apply csSup_le (s := {t : ℝ | t ∈ Set.Icc 0 1 ∧ formalOmega F 1 1 t = 2})
    ⟨0, ⟨le_rfl, zero_le_one⟩, formalOmega_one_one_zero F⟩
  rintro t ⟨ht, hω⟩
  exact h t ht hω

end SpectralBooks
end LinearAlgebra
end OAI
