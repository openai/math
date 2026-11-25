import OAI.Computability.BorderVNP.DiagonalPowerWords
import OAI.Computability.BorderVNP.DiagonalInitialGrid

/-! # Recovering the fine unary positions in a conditioned public box

The host cell map can identify any number of unary vertices. Each original
weight still reads its own fine incidence, conditional on the cell's private
assignment and on the acceptance of its local product.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.PowerWords

open Crossing
open scoped BigOperators Classical

variable {D b : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
    {Team Param Gadget : Type*} [Fintype Team] [Fintype Param] {tags : N.Tables (Entry Param Gadget)}
    (words : PowerWords Team Param Gadget b N tags)
    {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cell : N.Site → Cell) (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (hidden : ∀ i, N.InsideAssignment cell i)

/-- At the hosting cell read this occurrence at its original fine vertex.
At a different cell the same occurrence contributes zero. -/
noncomputable def hosted : (N.cellNetwork cell position).Tables (PowerSlot Team Param b → Bool) :=
  fun v a x w => if hw : cell (words.site w) = v then
    fineFactor cell words.selected v (hidden v) ⟨words.site w,hw⟩ a x w else false

omit [Fintype Cell] in
private theorem fine_false (v : Cell) (u : {i : N.Site // cell i = v}) (a x w)
    (hne : u.val ≠ words.site w) :
    fineFactor cell words.selected v (hidden v) u a x w = false := by
  cases hb : fineFactor cell words.selected v (hidden v) u a x w with
  | false => rfl
  | true => exact False.elim (hne (words.located u.val _ _ w hb).symm)

private theorem sum_hosted (v : Cell) (a x w) :
    (∑ u : {i : N.Site // cell i = v},
      slotPower w (fineFactor cell words.selected v (hidden v) u a x w)) =
    slotPower w (words.hosted cell position hidden v a x w) := by
  by_cases hw : cell (words.site w) = v
  · rw [hosted, dite_eq_left hw]
    apply Finset.sum_eq_single (⟨words.site w,hw⟩ : {i : N.Site // cell i = v})
    · intro u _ hne
      rw [words.fine_false cell hidden v u a x w (fun h => hne (Subtype.ext h)), slotPower_false]
    · simp
  · rw [hosted, dite_eq_right hw, slotPower_false]
    apply Finset.sum_eq_zero
    intro u _
    exact (congrArg (slotPower w) (words.fine_false cell hidden v u a x w
      (fun he => hw (he ▸ u.property)))).trans (slotPower_false _)

/-- Fixing one hidden assignment per cell yields a grouped power-word table.
The current public owner is the host cell of the original fine owner. -/
noncomputable def cellWords : PowerWords Team Param Gadget b
    (N.cellNetwork cell position) (conditionedCellTags cell position tags hidden) where
  site w := cell (words.site w)
  selected v a x w := if conditionedCellTags cell position tags hidden v a x ≠ 0 then
    words.hosted cell position hidden v a x w else false
  located v a x w h := by
    by_contra hn
    simp [hn, hosted] at h
  exact v a x := by
    by_cases hp : conditionedCellTags cell position tags hidden v a x ≠ 0
    · simp only [ite_eq_left hp]
      change (counters (∏ u : {i : N.Site // cell i = v}, fineFactor cell tags v (hidden v) u a x)).1 = _
      rw [counters_prod _ (fun u => Finset.prod_ne_zero_iff.mp hp u (Finset.mem_univ _)), counters_passed]
      have each (u : {i : N.Site // cell i = v}) :
          (counters (fineFactor cell tags v (hidden v) u a x)).1 =
            ∑ w, slotPower w (fineFactor cell words.selected v (hidden v) u a x w) :=
        words.exact u.val _ _
      simp_rw [each]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun w _ => words.sum_hosted cell position hidden v a x w
    · have hz := not_ne_iff.mp hp
      simp [hz, show counters (0 : Entry Param Gadget) = 0 from rfl]

section Uniform
variable {Q : Type} [Fintype Q] {origin finish : Q → N.Site} {S : ℕ}
    (packing : N.ChannelPacking origin finish S)

/-- Public channel addressing preserves every old owner. Failed padding resets
every selected occurrence at the affected box. -/
noncomputable def paddedWords : PowerWords Team Param Gadget b
    (N.uniformGrid origin finish S) (paddedFactor packing tags) where
  site := words.site
  selected v a x := if padOK packing v a x then unpackFactor packing words.selected v a x
    else fun _ => false
  located v a x w h := by
    by_cases hp : padOK packing v a x
    · rw [ite_eq_left hp] at h
      exact words.located v _ _ w h
    · simp [hp] at h
  exact v a x := by
    by_cases hp : padOK packing v a x
    · simp only [paddedFactor, ite_eq_left hp]
      exact words.exact v _ _
    · simp [paddedFactor, hp, show counters (0 : Entry Param Gadget) = 0 from rfl]

end Uniform

variable {Q : Type} [Fintype Q] {src dst : Q → Cell} {H : ℕ}
    (packing : (N.cellNetwork cell position).ChannelPacking src dst H)

/-- The public grid of conditioned private boxes carries every original
unary position, including coincident host cells and shared padded channels. -/
noncomputable def gridWords : PowerWords Team Param Gadget b
    ((N.cellNetwork cell position).uniformGrid src dst H)
    (conditionedGridTags cell position packing tags hidden) :=
  (words.cellWords cell position hidden).paddedWords packing

end Diagonal.CellEntries.PowerWords

end BorderVNP
end Computability
end OAI
