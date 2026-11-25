import OAI.Computability.IntegerMultiplication.Loom.Arrivals

/-! # Generating a unary field ruler within the full record volume -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveRulers
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Strip
open IntegerMultiplication.Loom IntegerMultiplication.Code

variable {X : Type} {r : Regime X} {n l : X → ℕ}

/-- Generate the unary layout size when it fits in the combined record volume. -/
theorem tape {t : X → Dims.Tape} (ht : Told r t) (pos : ∀ x, 1 ≤ n x)
    (volume : ∀ x, Dims.room (t x) ≤ n x * (l x + 1)) :
    Rip r n l r.header (fun x => send (tally (Dims.room (t x)))) := by
  apply Rip.relay pos _ (Rip.header pos ht.shape) (Dims.unary.on (fun x => ⟨t x, ht.solid x⟩))
  refine ⟨0, 2, fun x => ?_⟩
  change (Dims.room (t x) : ℝ) + 1 ≤ (2 : ℝ) * mass r n l 0 x
  have bound : (Dims.room (t x) : ℝ) ≤ mass r n l 0 x := by
    simp only [mass, pow_zero]
    exact_mod_cast volume x
  linarith [unit_mass (r := r) (l := l) pos 0 x]

/-- Generate the physical low-field ruler directly from its unary bit width. -/
theorem binary {b : X → ℕ} (hb : r.Has (tally ∘ b)) (pos : ∀ x, 1 ≤ n x)
    (volume : ∀ x, 2 ^ b x ≤ n x * (l x + 1)) :
    Rip r n l r.header (fun x => send (tally (2 ^ b x))) := by
  have room (x : X) : Dims.room (field 2 (b x)) = 2 ^ b x :=
    (Dims.space (field 2 (b x))).symm.trans (lineSize 2 (b x))
  simpa only [room] using tape (Told.carrier (q := 2) (by decide) b hb) pos
    (fun x => (room x).le.trans (volume x))

end Controlled.ReserveRulers

end NearSquareRoot
end Computability
end OAI
