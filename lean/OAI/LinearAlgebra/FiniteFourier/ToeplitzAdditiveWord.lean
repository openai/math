import OAI.LinearAlgebra.FiniteFourier.BorrowedComposition
import OAI.LinearAlgebra.FiniteFourier.CirculantWord
import OAI.LinearAlgebra.FiniteFourier.OccupiedWord
import OAI.LinearAlgebra.FiniteFourier.PaddingWords

/-! # Adding a Toeplitz product with occupied workspace

Signed padding and truncation surround a circulant addition. Each of the two
compositions restores its length-`b` intermediate array, so all workspace starts
with arbitrary contents and can be reused after the word.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K : Type*} [Field K] {a b D : ℕ} [NeZero b] {u : K}
  {W : Type} [Fintype W] [DecidableEq W]

/-- A rectangular Toeplitz addition over a protected ring. Both cyclic arrays
and the two Fourier workspaces are returned with their original contents. -/
theorem additiveWord_rectangularToeplitz_of_inverse {K : Type*} [CommRing K] {u : K} {e E : ℕ}
    {U : Matrix (Fin b) (Fin b) K} (hab : a + e ≤ b) (hu : u ^ b = 1)
    (hinv : U * geometricMatrix b u = 1)
    (hs : ∀ s : K, ∃ t : K, IsUnit t ∧ IsUnit (s-t)) (c : ℤ → K)
    (hF : OccupiedWord W D (geometricMatrix b u)) (hU : OccupiedWord W E U) :
    AdditiveWord (Fin b ⊕ (Fin b ⊕ (W ⊕ W))) (4*(E+D)+42) (rectangularToeplitz a e c) := by
  let src := Fin.castLEEmb (by omega : e ≤ b)
  let tgt := Fin.castLEEmb (by omega : a ≤ b)
  let J := (1 : Matrix (Fin b) (Fin b) K).submatrix (Equiv.refl _) src
  let R := (1 : Matrix (Fin b) (Fin b) K).submatrix tgt (Equiv.refl _)
  obtain ⟨v, hv⟩ := rectangularToeplitz_eq_compressed_circulant hab c
  change rectangularToeplitz a e c = R * circulant v * J at hv
  have hJ (s : Kˣ) : AdditiveWord (W ⊕ W) 3 ((s : K) • J) :=
    (layerWord_add_padding_of_pair src (s : K) (layerWord_transvection_unit (by decide) s)).occupied
  have hR (s : Kˣ) : AdditiveWord (W ⊕ W) 3 ((s : K) • R) :=
    (layerWord_add_truncation_of_pair tgt (s : K) (layerWord_transvection_unit (by decide) s)).occupied
  have hL (w : Fin b → K) : AdditiveWord (W ⊕ W) (E+6+D) (circulant w) :=
    layerWord_circulantShear_of_inverse hu hinv w hF hU (layerWord_diagShear_lower_of_unit_split hs _)
  rw [hv, show 4*(E+D)+42 = 2*(2*(3+(E+6+D))+3) by omega]
  exact AdditiveWord.mul_three (by simpa using hJ 1) (by simpa using hJ (-1))
    (hL v) (by rw [← circulant_neg]; exact hL (-v)) (by simpa using hR 1) (by simpa using hR (-1))

/-- Given an occupied-workspace word for the length-`b` Fourier transform, any
side-`a` Toeplitz addition takes at most `8 * D + 34` layer pairs. -/
theorem additiveWord_toeplitz_of_fourier (hab : 2 * a ≤ b) (hu : IsPrimitiveRoot u b)
    (c : ℤ → K) (hF : OccupiedWord W D (geometricMatrix b u)) :
    AdditiveWord (Fin b ⊕ (Fin b ⊕ (W ⊕ W))) (8 * D + 34) (toeplitzOfOffsets a c) := by
  let e := Fin.castLEEmb (by omega : a ≤ b)
  let J := (1 : Matrix (Fin b) (Fin b) K).submatrix (Equiv.refl _) e
  let R := (1 : Matrix (Fin b) (Fin b) K).submatrix e (Equiv.refl _)
  obtain ⟨v, hv⟩ := toeplitz_eq_compressed_circulant hab c
  change toeplitzOfOffsets a c = R * circulant v * J at hv
  have hJ (s : K) : AdditiveWord (W ⊕ W) 3 (s • J) :=
    (layerWord_add_padding e s).occupied
  have hR (s : K) : AdditiveWord (W ⊕ W) 3 (s • R) :=
    (layerWord_add_truncation e s).occupied
  have hL : AdditiveWord (W ⊕ W) (2 * D + 4) (circulant v) := layerWord_circulantShear hu v hF
  have hnL : AdditiveWord (W ⊕ W) (2 * D + 4) (-circulant v) := by
    rw [← circulant_neg]
    exact layerWord_circulantShear hu (-v) hF
  rw [hv, show 8 * D + 34 = 2 * (2 * (3 + (2 * D + 4)) + 3) by omega]
  exact AdditiveWord.mul_three (by simpa using hJ 1) (by simpa using hJ (-1))
    hL hnL (by simpa using hR 1) (by simpa using hR (-1))

end FiniteFourier
end LinearAlgebra
end OAI
