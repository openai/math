import OAI.Optimization.LinearProgramming.Geometry.GramAlgorithm
import OAI.Optimization.LinearProgramming.Compression.DetRamBits

/-! Separate the linear dependence on the input coefficient width from the
dimension powers in the row-basis and projector routines. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder

open Geometry Compression

private theorem bounded_monomials (z E d : ℕ) (hz : 0<z) (hE : 0<E) (k : ℕ) (hk : k≤d) :
    z^k≤E*z^d ∧ E*z^k≤E*z^d := by
  have h := Nat.pow_le_pow_right hz hk
  exact ⟨h.trans (Nat.le_mul_of_pos_left _ hE),Nat.mul_le_mul_left _ h⟩

theorem rowWidth_majorant (z E : ℕ) (hz : 0<z) (hE : 0<E) :
    let g := dotBitBound z E E
    E+g+detRegisterBits z g ≤ 128*E*z^4 := by
  have h := bounded_monomials z E 4 hz hE
  have h₀ := h 0 (by decide)
  have h₁ := h 1 (by decide)
  have h₂ := h 2 (by decide)
  have h₃ := h 3 (by decide)
  have h₄ := h 4 le_rfl
  dsimp only [dotBitBound,detRegisterBits]
  nlinarith only [h₀.1,h₀.2,h₁.1,h₁.2,h₂.1,h₂.2,h₃.1,h₃.2,h₄.1]

theorem gramWorkspaceBits_majorant (z E : ℕ) (hz : 0<z) (hE : 0<E) :
    gramWorkspaceBits z z E ≤ 640*E*z^6 := by
  have h := bounded_monomials z E 6 hz hE
  have h₀ := h 0 (by decide)
  have h₁ := h 1 (by decide)
  have h₂ := h 2 (by decide)
  have h₃ := h 3 (by decide)
  have h₄ := h 4 (by decide)
  have h₅ := h 5 (by decide)
  have h₆ := h 6 le_rfl
  dsimp only [gramWorkspaceBits,gramDetBits,dotBitBound]
  nlinarith only [h₀.1,h₀.2,h₁.1,h₁.2,h₂.1,h₂.2,h₃.1,h₃.2,h₄.1,h₄.2,h₅.1,h₅.2,h₆.1]

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
