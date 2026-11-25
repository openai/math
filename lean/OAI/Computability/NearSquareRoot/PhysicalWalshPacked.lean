import OAI.Computability.NearSquareRoot.KernelPassMixPhysical

/-! # Complete packed semantics of a fixed dyadic row mix -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshGrid

open IntegerMultiplication Code KernelPass KernelPassMix

variable {i o : ℕ}

def packed {w : ℕ} (r : Fin i → Coefficient) (x : Fin i → Dusk.Grain w) : Dusk.Grain w :=
  Grid.wrapMap w (Grid.content (Grid.fit (tally (w+1), Grid.rest (tally (denom r),
    accumulateRow r (List.ofFn (fun j => Dusk.mark (x j)))))))

theorem packed_eq {w : ℕ} (c : Fin o → Fin i → Coefficient) (x : Fin i → Dusk.Grain w) :
    mixMarked c (tally (w+1),List.ofFn fun j => Dusk.mark (x j)) =
      List.ofFn (fun b => Dusk.mark (packed (c b) x)) := by
  apply congrArg List.ofFn
  funext b
  exact Grid.spellG _ (Grid.fit_r _ _)

/-- A headroom certificate identifies the stored record with the correctly
rounded dyadic row sum. -/
theorem packed_eq_rounded {w : ℕ} (r : Fin i → Coefficient) (x : Fin i → Dusk.Grain w)
    (fit : Grid.focus w (Grid.divA (denom r) (accum r (Grid.aspect ∘ x)))) :
    packed r x = rounded r x := by
  unfold packed rounded
  rw [Grid.fit_small, Grid.rest_r, content_accumulateRow]
  rw [Grid.rest_r, content_accumulateRow]
  have h : (2:ℤ)^w ≤ 2^(w+1) := pow_le_pow_right₀ (by decide) (Nat.le_succ _)
  exact ⟨fit.1.trans_le h,fit.2.trans_le h⟩

end PhysicalWalshGrid

end NearSquareRoot
end Computability
end OAI
