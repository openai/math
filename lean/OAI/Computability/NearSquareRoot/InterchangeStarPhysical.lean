import OAI.Computability.NearSquareRoot.InterchangeStarCompile
import OAI.Computability.IntegerMultiplication.Loom.Horizon

/-!
# Physical address semantics of a compiled matrix

A single legal instruction list induces a permutation of every prime-power
address layout. The formula tracks all occupied fields and the prefix, gap, and
suffix indices. The stated cost counts cross-wing pivot calls in that list.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.CompilesOn

open IntegerMultiplication IntegerMultiplication.Strip.Dims IntegerMultiplication.Port
  IntegerMultiplication.Adic IntegerMultiplication.Loom Matrix

variable {I J : Type} [DecidableEq J] [Fintype I] {p n c : ℕ} [NeZero p]
    {slot : I → Spot J} {M : (f : ℕ) → Matrix I I (Tower p f)}

/-- Lift a matrix compiler certificate through the P192 physical address
permutation induced by its very same instruction list. -/
theorem physical (ord : J ≃ Fin n) (h : CompilesOn slot (ranking ord) c M) :
    ∃ (program : List (Lag J p)) (legal : ∀ op ∈ program, op.legal (ranking ord)),
      (program.map Lag.prices).sum ≤ c ∧
      ∀ (P G B : Tape) (f : ℕ) (x : Keys P G B J (Block p f)),
        let y := recreation ord P G B f program legal x
        watcher y = watcher x ∧
        (∀ i, hear (chase y) (slot i) = (M f *ᵥ (fun j => hear (chase x) (slot j))) i) ∧
        (∀ w, (∀ i, w ≠ slot i) → hear (chase y) w = hear (chase x) w) := by
  obtain ⟨program, legal, price, act⟩ := h
  refine ⟨program, legal, price, ?_⟩
  intro P G B f x
  dsimp only
  have hperm := fore ord program legal x
  have hfields := congrArg Prod.fst hperm
  change chase (recreation ord P G B f program legal x) = _ at hfields
  refine ⟨congrArg Prod.snd hperm, ?_⟩
  rw [hfields]
  exact act f (chase x)

end Interchange.CompilesOn

end NearSquareRoot
end Computability
end OAI
