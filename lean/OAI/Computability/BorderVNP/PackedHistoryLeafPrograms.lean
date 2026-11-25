import OAI.Computability.BorderVNP.PackedBankPrivateReplay
import OAI.Computability.BorderVNP.PackedHistoryFlatPrivateSites

/-! # Initial hypotheses in the original flat copy order

The existing nested presentation takes the actual independently supplied
programs of the flat leaves. Its restriction to a child is the same nested
presentation of that child's copies, so every hypothesis can be discharged
on the original individual inputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited Epoch.Round
open scoped Classical
attribute [local instance] portFintype

variable {D k : ℕ} {I P K : Type} [Fintype I] [Fintype P] {bits : P → ℕ} {A : ℕ → Type*} {depth : ℕ → ℕ}
  (view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n))

/-- Restricting the actual nested presentation returns the programs of the
corresponding flat child block, including the original per-copy ordering. -/
theorem subInitial_nested (n : ℕ) (flat : Fin (k^(n+1)) → A 0)
    (initial : ∀ z, Site.Programs (view 0 (flat z)).pack.layout) (j : Fin k) :
    subInitial (view := view) n (leavesEquiv k _ (n+1) flat)
      (nestedPrivatePrograms (fun x => (view 0 x).pack) (n+1) flat initial) j =
      nestedPrivatePrograms (fun x => (view 0 x).pack) n (fun i => flat (copyIndex k n (j,i)))
        (fun i => initial (copyIndex k n (j,i))) := by
  funext v
  rfl

set_option maxHeartbeats 1200000 in
/-- Genuine field or resource properties at each original flat input imply
the corresponding base hypotheses on the nested replay. -/
theorem nestedLeaves_within (good : ∀ n (x : A n), Site.Programs (view n x).pack.layout → Prop)
    (n : ℕ) (flat : Fin (k^n) → A 0) (initial : ∀ z, Site.Programs (view 0 (flat z)).pack.layout)
    (hb : ∀ z, good 0 (flat z) (initial z)) :
    LeavesWithin (view := view) good n (leavesEquiv k _ n flat)
      (nestedPrivatePrograms (fun x => (view 0 x).pack) n flat initial) := by
  induction n with
  | zero =>
    dsimp only [LeavesWithin,nestedPrivatePrograms]
    change good 0 (flat 0) _
    refine (congrArg (good 0 (flat 0)) ?_).mpr (hb 0)
    funext v
    rfl
  | succ n ih =>
    intro j
    let sub := fun i => flat (copyIndex k n (j,i))
    let init := fun i => initial (copyIndex k n (j,i))
    change LeavesWithin (view := view) good n (leavesEquiv k _ n sub)
      (subInitial (view := view) n _ (nestedPrivatePrograms _ (n+1) flat initial) j)
    rw [subInitial_nested]
    exact ih sub init (fun i => hb (copyIndex k n (j,i)))

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
