import OAI.Hierarchy.GridThroughPinAssignment
import OAI.Hierarchy.FactorOccurrences
import OAI.Hierarchy.GridTickAddresses

namespace OAI
/-! # The interval pin assignment for the original factor-occurrence dispatch -/

namespace Hierarchy.FactorPinIntervals

open GridThrough
noncomputable section

variable {E : Type} {S N k n q d m : ℕ}

variable (ht : 0<(n+1)^k*q) (w : ℕ) (cost : Fin N → Fin m → ℕ)
    (origin : Fin S → Fin N) (header : (GridThrough.Cell k n × Fin q) → List Bool) (advice : Fin S → Bool)
    (room : ∀ t : GridThrough.Cell k n × Fin q, (header t).length +
      ((FactorAllocation.factors w cost (List.finRange N) (GridTicks.index t)).map
        (fun i => (Finset.univ.filter (fun j => origin j=i)).card)).sum ≤ d)

/-- The owning tick and the ordered occurrence lists are computed by the actual
geometric-bucket allocator. The sole pin-budget bound counts the original input bits. -/
def scheduledLayout : Layout (GridThrough.Cell k n × Fin q) S N d where
  origin := origin
  owner i := GridTicks.index.symm (FactorAllocation.owner ht w cost i)
  rows t := FactorAllocation.factors w cost (List.finRange N) (GridTicks.index t)
  owns i t := by
    rw [FactorAllocation.mem_factors_iff_owner ht w cost]
    exact ⟨fun h => by rw [←h,Equiv.symm_apply_apply],
      fun h => by rw [←h,Equiv.apply_symm_apply]⟩
  distinct t := FactorAllocation.factors_nodup ht w cost _
  header := header
  advice := advice
  fits := room

/-- Any finite set of labelled external pairs embedded at original pair ordinals
inherits its two allocated pins from the physical trace's paired-owner property. -/
def scheduledPins (rail : E ↪ Fin (S/2)) (direction : E → Fin k)
    (whole : ∀ (i : ℕ) (hi : 2*i+1<S),
      origin ⟨2*i, by omega⟩ = origin ⟨2*i+1,hi⟩) :
    GridThrough.PinAssignment E k n q d := by
  apply GridThrough.PinAssignment.ofFactorIntervals
    (scheduledLayout ht w cost origin header advice room) direction (pairPorts rail)
  intro e
  apply Eq.symm
  exact whole (rail e).val (by have := (rail e).isLt; omega)

end
end Hierarchy.FactorPinIntervals

end OAI
