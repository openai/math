import OAI.Computability.NearSquareRoot.InterchangeBQuestResolve
import OAI.Computability.NearSquareRoot.InterchangeSpacePotential

/-! # Recursive commands with two kinds of child calls

A contracted call may share the deck with an entire parent row. A call on a
full row shares it with a logarithmic-size descriptor. Both kinds of calls use
the same physical recursive command.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom Space

structure Mixed {I X : Type} (job : Job X) (small full : I → List X) (V : I → ℕ)
    (input output : I → Tree) : Prop where
  build : ∃ (cmd : Cmd) (C H : ℕ), ∀ (i : I) (parent : Cmd) (env : Env) (time data depth : X → ℕ),
    (∀ y ∈ small i ++ full i, ∀ d b, DeckCap b d →
      BoundedFits (parent :: env) parent (pile 0 (job.issue y) d) (pile 0 (job.reply y) d)
        (time y) (b + data y) (depth y)) →
    ∀ deck base, DeckCap base deck →
      BoundedFits (parent :: env) cmd (pile 0 (input i) deck) (pile 0 (output i) deck)
        (C * V i + ((small i ++ full i).map time).sum)
        (base + max (C * V i + childPeak data (small i))
          (H * (Nat.log 2 (V i) + 1) + childPeak data (full i)))
        (max (C * V i + childPeak depth (small i))
          (H * (Nat.log 2 (V i) + 1) + childPeak depth (full i)))

end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
