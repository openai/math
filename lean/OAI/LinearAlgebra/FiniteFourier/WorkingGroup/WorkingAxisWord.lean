import OAI.LinearAlgebra.FiniteFourier.GridFactorWord
import OAI.LinearAlgebra.FiniteFourier.WorkingGroup

/-! # The second application of the occupied-workspace Toeplitz word

A working-length Fourier transform uses at most fourteen registers per data
coordinate. The word for one original axis therefore fits in one hundred
and seventy registers per coordinate, uniformly in the side length.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace WorkingGroup

variable {K E : Type*} [Field K] [Field E] {ι : Type*}
  {a : ι → ℕ} {t d : ℕ} (w : WorkingGroup K a t)

/-- Convert the working-length Fourier word into the requested axis factor. -/
theorem axis_word_of_length_word (i : ι) {u : E} (hu : IsPrimitiveRoot u (w.length i))
    (hF : OccupiedWord (Fin (13*w.length i)) d (geometricMatrix (w.length i) u))
    {A : Matrix (Fin (a i)) (Fin (a i)) E} (hA : GridFactor A) :
    OccupiedWord (Fin (169*a i)) (336*d+1463) A := by
  have hlo : 2*a i ≤ w.length i := (w.axes i).lower
  have hhi : w.length i < 6*a i := (w.axes i).upper
  have h := gridFactor_word_of_fourier (by omega : 0 < a i) hlo hu hF hA
  apply LayerWord.enlargeWorkspace h
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end WorkingGroup

end FiniteFourier
end LinearAlgebra
end OAI
