import OAI.Computability.NearSquareRoot.InterchangeBeadRadix

/-!
# Binary rectangular interchange at every exponent above one half

The native program supplies one radix for all header regimes and payloads. The
binary halo operations convert it to the existing rectangular tape interface.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Loom

/-- Interchange two binary fields of the same width, retaining arbitrary
prefix, gap, suffix and payload series covered by the P192 rectangular interface. -/
theorem nearRoot_rectInterchange {α : ℝ} (hα : 1/2 < α) {I : Type} (r : Regime I) (n : I → ℕ) :
    RectInterchange r n α := by
  obtain ⟨b,hb,large,radix⟩ := InterchangePayload.exists_radix_beads hα Net.Shuttle.base
  let _ : NeZero b := ⟨hb.ne_zero⟩
  exact InterchangeBinary.rect_of_radix n (by linarith) hb.two_le large.le (radix r)

/-- The same time charge for P192's native encoding of arbitrary binary
words of equal length, including the empty word. -/
theorem nearRoot_bitstring_swap {α : ℝ} (hα : 1/2 < α) {I : Type} {r : Regime I}
    (P G B : I → Tape) (n : I → ℕ) (hn : r.Has (tally ∘ n))
    (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (guard : ∀ i d, d ∈ P i ++ G i ++ B i → d ≤ Net.Shuttle.base)
    (L width : I → ℕ) (bound : ∀ i, width i ≤ L i)
    (v : (i : I) → SpanKey (P i) (G i) (B i) (Block 2 (n i)) → List Bool)
    (exactWidth : ∀ i x, (v i x).length = width i) :
    let s i := stock 2 (P i) (G i) (B i) (n i)
    Breeze (Spindle.modes n (τ:=α)) r (fun i => (s i).count) L
      (together r.header (stackRun s fun i x => send (v i x)))
      (stackRun s fun i x => send (v i (swapper _ _ _ x))) :=
  InterchangeBinary.bitstrings P G B n (nearRoot_rectInterchange hα r n)
    hn hp hg hs guard L width bound v exactWidth

end Controlled

end NearSquareRoot
end Computability
end OAI
