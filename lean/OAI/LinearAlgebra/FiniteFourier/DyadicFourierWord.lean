import OAI.LinearAlgebra.FiniteFourier.DyadicFourierToeplitz
import OAI.LinearAlgebra.FiniteFourier.DyadicToeplitzWord
import Mathlib.Data.Nat.Log

/-! # Protected Fourier words of arbitrary order

The auxiliary FFT uses the least power of two or three at least twice the
input width. Both transform directions use at most thirteen auxiliary
registers per input register.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R : Type*} [CommRing R] {a B r : ℕ}

private theorem protected_padding (hr : r = 2 ∨ r = 3) (ha : 0 < a) (haB : a ≤ B) :
    let j := Nat.clog r (2*a)
    2*a ≤ r^j ∧ r^j ≤ 6*a ∧ j ≤ 1 + Nat.clog 2 (2+B) := by
  have hr₂ : 2 ≤ r := by omega
  have hr₃ : r ≤ 3 := by omega
  let j := Nat.clog r (2*a)
  have hj : 0 < j := Nat.clog_pos (by omega) (by omega)
  refine ⟨Nat.le_pow_clog (by omega) _, ?_, ?_⟩
  · have hlt := Nat.pow_pred_clog_lt_self (by omega : 1 < r) (show 1 < 2*a by omega)
    change r ^ j.pred < 2*a at hlt
    change r ^ j ≤ 6*a
    rw [← Nat.succ_pred_eq_of_pos hj, pow_succ]
    exact (Nat.mul_le_mul hlt.le hr₃).trans (by omega)
  · apply Nat.clog_le_of_le_pow
    rw [pow_add, pow_one]
    have h := (Nat.le_pow_clog (by decide : 1 < 2) (2+B)).trans
      (Nat.pow_le_pow_left hr₂ _)
    exact Nat.mul_le_mul hr₂ (by omega)

/-- A protected forward or inverse transform at unit-separated nodes, with a
depth bound uniform over the ring, the radix, and every width up to `B`. -/
theorem protectedFourier_word_up_to
    (hr : r = 2 ∨ r = 3) (ha : 0 < a) (haB : a ≤ B)
    (hroots : ∀ j, r^j ≤ 8*B → IsUnit ((r^j : ℕ) : R) ∧ ∃ u : Rˣ, u^(r^j) = 1 ∧
      Pairwise fun i k : Fin (r^j) ↦ IsUnit ((u : R)^i.val - (u : R)^k.val))
    (hs : ∀ s : R, ∃ t : R, IsUnit t ∧ IsUnit (s-t)) {q : R} (hq : IsUnit q)
    (hsep : Pairwise fun i j : Fin a ↦ IsUnit (q^i.val - q^j.val))
    {A : Matrix (Fin a) (Fin a) R} (hA : A = geometricMatrix a q ∨ A = (geometricMatrix a q)⁻¹) :
    OccupiedWord (Fin (13*a)) (6400*(1 + Nat.clog 2 (2+B))) A := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    unfold OccupiedWord
    rw [Subsingleton.elim (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin (13*a)) (Fin (13*a)) R)) 1]
    exact layerWord_one _
  | inr h =>
    let j := Nat.clog r (2*a)
    obtain ⟨hb₁, hb₂, hj⟩ := protected_padding hr ha haB
    change 2*a ≤ r^j at hb₁
    change r^j ≤ 6*a at hb₂
    change j ≤ 1 + Nat.clog 2 (2+B) at hj
    obtain ⟨hb,u,hu,hp⟩ := hroots j (by omega)
    have hadd := protected_rectangularToeplitz_word (a := a) (e := a) hr j (by omega) u hu hb hp hs
    have hd (k : ℕ) (hk : 0 < k) (hka : k < a) : IsUnit ((u : R)^k - 1) := by
      let i : Fin (r^j) := ⟨k, by omega⟩
      let z : Fin (r^j) := ⟨0, by omega⟩
      have hiz : i ≠ z := fun e ↦ hk.ne' (congrArg Fin.val e)
      simpa [i, z] using hp hiz
    obtain ⟨l, hl, hf, rfl⟩ := protectedGeometric_and_inverse_factors hq hsep A hA
    have hw := occupiedWord_list_prod l fun M hM ↦ protectedNewtonFactor_word_of_additive ha u hd hadd (hf M hM)
    rw [hl] at hw
    apply LayerWord.pad _ (hw.enlargeWorkspace (V := Fin (13*a)) ?_)
    · omega
    · simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_empty, add_zero]
      omega

end FiniteFourier
end LinearAlgebra
end OAI
