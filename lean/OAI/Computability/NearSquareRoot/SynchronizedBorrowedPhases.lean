import OAI.Computability.NearSquareRoot.SynchronizedPrimitive
import OAI.Computability.NearSquareRoot.SynchronizedShortTransform

/-! # Phase and reflection layers on the borrowed workspace

The short fiber occupies the first `a` cells of the first half of the
workspace. Both reflection signs and all three outer chirp diagonals are
full phase tables, with explicit entries on every borrowed cell.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix Finset
open scoped Matrix

private def place {a r : ℕ} (har : a ≤ r) (j : Fin a) : Fin r ⊕ Fin r :=
  Sum.inl (j.castLE har)

private theorem active_entry {a r : ℕ} (har : a ≤ r) (x : Fin r ⊕ Fin r) (j : Fin a) :
    activeFiber har x j = if x = place har j then 1 else 0 := by
  cases x <;> simp [activeFiber, firstHalfInclusion, fromRows, Sum.elim, firstCoords, place]

/-- Local array table obtained from the active fiber and one constant for all
borrowed cells, in the original coordinate order. -/
def fiberEntries {a r : ℕ} (d : Fin a → ℂ) (z : ℂ) : Fin r ⊕ Fin r → ℂ
  | Sum.inl j => if hj : j.val < a then d ⟨j.val, hj⟩ else z
  | Sum.inr _ => z

private theorem fiberEntries_inside {a r : ℕ} (har : a ≤ r) (d : Fin a → ℂ) (z : ℂ) (i : Fin a) :
    fiberEntries d z (place har i) = d i := by
  simp [place, fiberEntries]

private theorem fiberEntries_outside {a r : ℕ} (har : a ≤ r) (d : Fin a → ℂ) (z : ℂ)
    (x : Fin r ⊕ Fin r) (hx : x ∉ Set.range (place har)) : fiberEntries d z x = z := by
  cases x with
  | inr j => rfl
  | inl j =>
    have hja : ¬j.val < a := fun hj => hx ⟨⟨j.val,hj⟩,rfl⟩
    simp [fiberEntries, hja]

/-- Extending a diagonal by zero writes the supplied entry at each active
cell and zero at every other cell. -/
private theorem active_weighted {a r : ℕ} (har : a ≤ r) (d : Fin a → ℂ) :
    activeFiber har * diagonal d * (activeFiber har)ᴴ = diagonal (fiberEntries d 0) := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, active_entry]
  by_cases hx : x ∈ Set.range (place har)
  · obtain ⟨j, rfl⟩ := hx
    rw [sum_eq_single j]
    · by_cases hy : place har j = y
      · subst y
        simp [fiberEntries_inside]
      · simp [hy, Ne.symm hy]
    · intro b _ hb
      have hne : place har j ≠ place har b := fun h =>
        hb (Fin.ext (congrArg Fin.val (Sum.inl.inj h)).symm)
      simp [hne]
    · simp
  · have hne (j : Fin a) : x ≠ place har j := fun h => hx ⟨j,h.symm⟩
    simp [hne, Matrix.diagonal_apply, fiberEntries_outside har _ _ _ hx]

/-- The exact table is read on the first `a` addresses, and all remaining
addresses receive the identity phase. -/
theorem extend_active_diagonal {a r : ℕ} (har : a ≤ r) (d : Fin a → ℂ) :
    extend (activeFiber har) (diagonal d) = diagonal (fiberEntries d 1) := by
  have shift : diagonal d - 1 = diagonal (fun j => d j - 1) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  rw [extend, shift, active_weighted, ← Matrix.diagonal_one, Matrix.diagonal_add]
  apply congrArg
  funext x
  by_cases hx : x ∈ Set.range (place har)
  · obtain ⟨j, rfl⟩ := hx
    simp [fiberEntries_inside]
  · simp [fiberEntries_outside har _ _ _ hx]

/-- A diagonal on the active coordinates extends to a single phase table. -/
theorem shortLayer_extend_phase {a r : ℕ} (har : a ≤ r) (d : Fin a → ℂ)
    (hd : ∀ j, ‖d j‖ = 1) :
    ShortLayer (extend (activeFiber har) (diagonal d)) := by
  rw [extend_active_diagonal]
  refine .phase _ fun x => ?_
  by_cases hx : x ∈ Set.range (place har)
  · obtain ⟨j, rfl⟩ := hx
    simpa only [fiberEntries_inside] using hd j
  · simp [fiberEntries_outside har _ _ _ hx]

/-- The two reflection signs on the active cell projector. -/
theorem shortLayer_reflection_pair {a r : ℕ} (har : a ≤ r) :
    let E := activeFiber har
    ShortLayer ((2 : ℝ) • (E * Eᴴ) - 1) ∧ ShortLayer (1 - (2 : ℝ) • (E * Eᴴ)) := by
  dsimp only
  have hp : activeFiber har * (activeFiber har)ᴴ =
      diagonal (fiberEntries (fun _ : Fin a => 1) 0) := by
    simpa only [Matrix.diagonal_one, Matrix.mul_one] using
      active_weighted har (fun _ : Fin a => 1)
  rw [hp, ← Matrix.diagonal_smul, ← Matrix.diagonal_one,
      Matrix.diagonal_sub, Matrix.diagonal_sub]
  constructor <;> apply ShortLayer.phase <;> intro x <;>
    by_cases hx : x ∈ Set.range (place har)
  all_goals first
    | obtain ⟨j, rfl⟩ := hx; norm_num [fiberEntries_inside]
    | norm_num [fiberEntries_outside har _ _ _ hx]

end ShortFourier

end NearSquareRoot
end Computability
end OAI
