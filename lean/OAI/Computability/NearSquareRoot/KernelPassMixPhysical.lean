import OAI.Computability.NearSquareRoot.KernelPassMix
import OAI.Computability.NearSquareRoot.KernelPassMixNorm
import OAI.Computability.NearSquareRoot.KernelPassMixBanks

/-! # A physical fixed-coefficient pass on complete banks of complex dyadics

The program is fixed by the coefficient matrix. The address count and the record
width are supplied on two rulers. Encoded records of all input rows enter in
row order and the rounded outputs leave in the same order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPassMix

open IntegerMultiplication IntegerMultiplication.Code KernelPass MixBankLayout

variable {α : Type} {i o : ℕ}

/-- Serialized rows of fixed-width signed dyadics. -/
def markedBank {k w : ℕ} (addresses : List α) (x : α → Fin k → Dusk.Grain w) :
    List (List Dusk.Pair) := bank addresses (fun a j => Dusk.mark (x a j))

variable {J : Type} {β : J → Type}

/-- The same command runs at all address counts and record widths.
Its clock includes gathering the rows, evaluation, and restoring their layout. -/
theorem mixBankTask (c : Fin o → Fin i → Coefficient) (l : (t : J) → List (β t)) (w : J → ℕ)
    (x : (t : J) → β t → Fin i → Dusk.Grain (w t))
    (headroom : ∀ t, ∀ a ∈ l t, ∀ b,
      Grid.focus (w t) (Grid.divA (denom (c b)) (accum (c b) (Grid.aspect ∘ x t a)))) :
    Task (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => send ((tally (l t).length, tally (w t + 1)), markedBank (l t) (x t)))
      (fun t => send (markedBank (l t) (fun a b => rounded (c b) (x t a)))) := by
  apply KernelPassMixBanks.mixBanks ([], []) ([], []) (mixMarked c) (mixMarked_easy c)
    l w (fun t a j => Dusk.mark (x t a j)) (fun t a b => Dusk.mark (rounded (c b) (x t a))) 7
  · intro t a _ j
    rw [Dusk.volume]
    omega
  · intro t a ha
    exact mixMarked_exact c _ (headroom t a ha)

/-- The header-preserving command composes with other operations on the same bank.
The bounds cover all live register data and additional return addresses. -/
theorem mixHeaderBoundedTask (c : Fin o → Fin i → Coefficient) (l : (t : J) → List (β t))
    (w : J → ℕ) (x : (t : J) → β t → Fin i → Dusk.Grain (w t))
    (headroom : ∀ t, ∀ a ∈ l t, ∀ b,
      Grid.focus (w t) (Grid.divA (denom (c b)) (accum (c b) (Grid.aspect ∘ x t a)))) :
    Space.BoundedTask (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => send ((tally (l t).length, tally (w t + 1)), markedBank (l t) (x t)))
      (fun t => send ((tally (l t).length, tally (w t + 1)),
        markedBank (l t) (fun a b => rounded (c b) (x t a)))) := by
  apply KernelPassMixBanks.bounded_mixBanks_header ([], []) ([], []) (mixMarked c) (mixMarked_easy c)
    l w (fun t a j => Dusk.mark (x t a j)) (fun t a b => Dusk.mark (rounded (c b) (x t a))) 7
  · intro t a _ j
    rw [Dusk.volume]
    omega
  · intro t a ha
    exact mixMarked_exact c _ (headroom t a ha)

/-- The fixed-tape implementation of the row-mixing primitive. The time bound
counts actual tape transitions and only the result tape can change on return. -/
theorem physicalMix (c : Fin o → Fin i → Coefficient) (l : (t : J) → List (β t)) (w : J → ℕ)
    (x : (t : J) → β t → Fin i → Dusk.Grain (w t))
    (headroom : ∀ t, ∀ a ∈ l t, ∀ b,
      Grid.focus (w t) (Grid.divA (denom (c b)) (accum (c b) (Grid.aspect ∘ x t a)))) :
    ShortWord.PhysicalTask (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => send ((tally (l t).length, tally (w t + 1)), markedBank (l t) (x t)))
      (fun t => send (markedBank (l t) (fun a b => rounded (c b) (x t a)))) :=
  ShortWord.physicalTask (mixBankTask c l w x headroom)

/-- The physical bank outputs are exactly the records measured against the
complex matrix of the corresponding DSL instruction in `round_mix_error`. -/
theorem rounded_eq_roundedMix {A h w : ℕ} (c : Fin o → Fin i → Coefficient)
    (x : Fin i × Addr A h → Dusk.Grain w) (b : Fin o) (a : Addr A h) :
    rounded (c b) (fun j => x (j,a)) = roundedMix w c x (b,a) := rfl

/-- A bounded realization of the mix instruction at varying binary-address widths.
The row representation on return is the one in the Euclidean correctness theorem. -/
theorem planMixBoundedTask {A : ℕ} (c : Fin o → Fin i → Coefficient) (h w : J → ℕ)
    (l : (t : J) → List (Addr A (h t)))
    (x : (t : J) → Fin i × Addr A (h t) → Dusk.Grain (w t))
    (fits : ∀ t, ∀ a ∈ l t, ∀ b,
      ‖Grid.toC (accum (c b) (Grid.aspect ∘ (fun j => x t (j,a)))) / (2 : ℂ)^denom (c b)‖ <
        (2 : ℝ)^(w t)) :
    Space.BoundedTask (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => send ((tally (l t).length, tally (w t + 1)),
        markedBank (l t) (fun a j => x t (j,a))))
      (fun t => send ((tally (l t).length, tally (w t + 1)),
        markedBank (l t) (fun a b => roundedMix (w t) c (x t) (b,a)))) :=
  mixHeaderBoundedTask c l w (fun t a j => x t (j,a))
    (fun t a ha b => divA_fits _ _ _ (fits t a ha b))

end KernelPassMix

end NearSquareRoot
end Computability
end OAI
