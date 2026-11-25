import OAI.Computability.NearSquareRoot.CRTControlledEffectiveRect

/-! # Installing the binary rectangle header in a packed program

A fixed header pass prepares the physical interchange request. The registry
command occupies the rectangle leaf, uniformly over its descriptor exponent.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Effective

open IntegerMultiplication Code Strip Strip.Dims Loom Adic NamedPacked InterchangeROMBinary

/-- The single physical binary interchange file may use its own polynomial
exponent for header processing. -/
def rectContract (c : Cmd) (ρ : ℝ) : Prop := ∃ D, RectPhysical c ρ D

/-- Convert an arbitrary represented P/G/B description to the rectangle's
canonical header. This preprocessor is chosen before the child file and its
exponent. The same template runs every record stream indexed by `X`. -/
theorem rectangleProgram {X : Type} {r : Regime X} (P G B : X → Tape) (n : X → ℕ)
    (hn : r.Has (tally ∘ n)) (hp : Told r P) (hg : Told r G) (hb : Told r B)
    (guard : ∀ x d, d ∈ P x ++ G x ++ B x → d ≤ Net.Shuttle.base)
    (l : X → ℕ) {T : X → Type} (u : (x : X) → Series (T x)) (len : ∀ x, (u x).count ≤ l x)
    (v : (x : X) → SpanKey (P x) (G x) (B x) (Block 2 (n x)) → T x → Bead) :
    let s x := stock 2 (P x) (G x) (B x) (n x)
    Program rectContract n r (fun x => (s x).count) l
      (together r.header (cloth s u v)) (cloth s u fun x a => v x (swapper _ _ _ a)) := by
  obtain ⟨pre,go⟩ := rectEmitter P G B n hn hp hg hb guard
  refine ⟨.next (.fixed pre) .rectangle,fun c ρ hρ ⟨D,run⟩ => ?_⟩
  exact go ρ c D hρ run l u len v

end Controlled.Effective

end NearSquareRoot
end Computability
end OAI
