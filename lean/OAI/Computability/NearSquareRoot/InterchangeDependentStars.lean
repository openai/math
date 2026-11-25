import OAI.Computability.NearSquareRoot.InterchangeStarCompile

/-!
# Compiling a family of address changes with different active slots

Each rational change is factored on its own finite active-slot type. The
common prime and token table work for all addresses and widths, while the
number of pivot calls depends only on the currently active dimension.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open IntegerMultiplication.Port Matrix

/-- Compile all members into the same prime radix. Each program fixes slots
outside its injection and charges at most eighteen pivots per active slot. -/
theorem compile_dependent_matrix_family {T : Type*} [Fintype T] {I : T → Type}
    [∀ t, DecidableEq (I t)] [∀ t, Fintype (I t)] (W : ℕ) (extra : Finset ℚ)
    (A : (t : T) → Matrix (I t) (I t) ℚ) (hA : ∀ t, IsUnit (A t)) :
    ∃ b : ℕ, b.Prime ∧ W < b ∧ ∃ code : ℚ → Pinpoint b,
      (∀ x ∈ extra, (code x = none ↔ x = 0) ∧ ∀ f, Token x ((code x).stamp f)) ∧
      ∀ t, ∃ M : (f : ℕ) → Matrix (I t) (I t) (Tower b f),
        (∀ f, MatrixToken (A t) (M f)) ∧
        ∀ {J : Type} [DecidableEq J] (slot : I t → Spot J) (_ : Function.Injective slot)
          (rank : J → ℕ) (_ : Function.Injective rank), CompilesOn slot rank (18 * Fintype.card (I t)) M := by
  obtain ⟨b, hb, hw, code, hex, hall⟩ := exists_dependent_star_family W extra A hA
  refine ⟨b, hb, hw, code, hex, fun t => ?_⟩
  obtain ⟨l,r,d,hl,hr,hc,he⟩ := hall t
  refine ⟨_, he, fun {J} _ slot inj rank jr => ?_⟩
  obtain lprog := compile_stars slot inj rank jr code l hl
  obtain rprog := compile_stars slot inj rank jr code r hr
  have dprog := compile_diagonal slot inj rank d
  apply ((lprog.mul dprog).mul rprog).mono
  omega

end Interchange

end NearSquareRoot
end Computability
end OAI
