import OAI.Computability.BorderVNP.DiagonalInitialGridRouted
import OAI.Computability.BorderVNP.DiagonalPowerCopies

/-! # The initial repeated public grid of the shortening history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridPlacement

open Crossing Diagonal.CellEntries Shortening
open scoped BigOperators Classical

variable {D b : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    {G J : Type} [Group G] [Fintype G] [Fintype J]
    {place : N.Site → G} {step : J → G} {invStep : ∀ j, ∃ k, step k = (step j)⁻¹} {k h : ℕ}
    (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (r : Routed N place step invStep k h) (unit : ∀ e, N.width e ≤ 1)
    {Team Param Gadget E : Type*} [Fintype Team] [Fintype Param]
    {tags : N.Tables (Entry Param Gadget)} (sites : PowerSites Team Param Gadget b N tags)
    {copies : ℕ} (z : Fin copies → PrivateAssignments position r)

/-- A separate hidden fine assignment in each slice of the repeated public grid.
Each copy retains all its original unary occurrences. -/
noncomputable def privateBundleWords :
    PowerWords (Fin copies × Team) Param Gadget b
      ((N.cayleyGrid place position step (cableWidth G k h)).repeatGrid copies)
      (repeatedTags (fun i => privateGridTags position r unit tags (z i))) :=
  PowerWords.repeated _ fun i => privateGridWords position r unit sites (z i)

/-- The public cell of a fine unary occurrence is the same on every grid slice. -/
theorem privateBundleWords_site (w : PowerSlot (Fin copies × Team) Param b) :
    (privateBundleWords position r unit sites z).site w = place (sites.site (w.1.2,w.2)) := rfl

omit [Fintype Param] in
/-- The complete bottom bundle sums one hidden assignment per copy, on top
of its public repeated-width cable words, to recover the exact product of
the fine batch tensors on all copy-indexed external ports. -/
theorem sum_privateBundle_value [CommSemiring E] (values : Gadget → E)
    (x : Ports (fun p : Fin copies × P => bits p.2)) :
    (∑ z : Fin copies → PrivateAssignments position r,
      ((N.cayleyGrid place position step (cableWidth G k h)).repeatGrid copies).value
        (fun v a y => interpret values (repeatedTags (fun i => privateGridTags position r unit tags (z i)) v a y)) x) =
      ∏ i, N.value (fun v a y => interpret values (tags v a y)) (fun p => x (i,p)) := by
  simp_rw [value_repeatedTags]
  symm
  calc
    _ = ∏ i, ∑ z : PrivateAssignments position r,
        (N.cayleyGrid place position step (cableWidth G k h)).value
          (fun v a y => interpret values (privateGridTags position r unit tags z v a y)) (fun p => x (i,p)) :=
      Finset.prod_congr rfl fun _ _ => (sum_privateGrid_value position r unit values _).symm
    _ = _ := Fintype.prod_sum _

include r unit sites in
/-- The seed of the packing history with its finite hidden term type. Its
local tags serve in every coefficient ring and for every external input. -/
theorem exists_privateBundle_terms (copies : ℕ) :
    let M := (N.cayleyGrid place position step (cableWidth G k h)).repeatGrid copies
    ∃ (Hidden : Type) (_ : Fintype Hidden) (term : Hidden → M.Tables (Entry Param Gadget)),
      (∀ z, Nonempty (PowerWords (Fin copies × Team) Param Gadget b M (term z))) ∧
      ∀ (E : Type*) [CommSemiring E] (values : Gadget → E) (x : Ports (fun p : Fin copies × P => bits p.2)),
        (∑ z, M.value (fun v a y => interpret values (term z v a y)) x) =
          ∏ i, N.value (fun v a y => interpret values (tags v a y)) (fun p => x (i,p)) := by
  refine ⟨Fin copies → PrivateAssignments position r, inferInstance,
    fun z => repeatedTags (fun i => privateGridTags position r unit tags (z i)), ?_, ?_⟩
  · exact fun z => ⟨privateBundleWords position r unit sites z⟩
  · intro E _ values x
    have hh := sum_privateBundle_value (tags := tags) position r unit values x
    exact (Finset.sum_congr (Finset.ext fun _ => by simp) fun _ _ => rfl).trans hh

end Packing.GridPlacement

end BorderVNP
end Computability
end OAI
