import OAI.Computability.BorderVNP.FiniteDiagonalCubeHost
import OAI.Computability.BorderVNP.FinitePrewireAssigned

/-! # Fully assigned cube terms of the prewired finite-field grid

Within-team physical wires are contracted when the batch is prewired. The
independent indices left after packet substitution are the exterior links,
the actual adaptive history, and a private, singleton, and cube assignment
for that history's real network and slot directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FinitePrewire

open Crossing Packing ParseBatch.Prewire TeamContraction FieldTeam FiniteDiagonal
open scoped BigOperators Classical

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000

variable {D R r t d link inner n b K h : ℕ} {Edge : Type} [Fintype Edge]
  {F : Type*} [Field F] [Fintype F]
  (T : Wiring R r t d link inner n Edge)
  (e : PackPorts Unit b K h ≃ Fin (R+1))
  (H : ProfileSum (ValuedPack F D (packWidth (fun _ : Fin r × Fin (publicWidth T) => 1) b K h)))
  (plans : ∀ i : H.Index, FieldPacketPlan (H.term i).1 F)

/-- One complete term after the section 8.2 replacement, with the copied
input bits supplied by its own shared exterior assignment. -/
abbrev GridCubeTerm (R r link : ℕ) {P : Type} {bits : P → ℕ}
    (H : ProfileSum (ValuedPack F D bits)) (plans : ∀ i : H.Index, FieldPacketPlan (H.term i).1 F) :=
  (Exterior R r link → Bool) × (i : H.Index) × (plans i).Path

/-- Actual host and selected cube factors of a term with its true public input. -/
noncomputable def gridCubeWeight (pin : Fin d → Bool) (a : GridCubeTerm R r link H plans) : F :=
  (plans a.2.1).weight (H.term a.2.1).2 (historyPorts T e pin a.1) a.2.2

omit [Fintype Edge] [Fintype F] in
/-- Section 8.2 gives an equality of sums between the independent packet
assignments and the original wires of all selected histories. -/
theorem sum_gridCubeWeight (pin : Fin d → Bool) :
    (∑ a : GridCubeTerm R r link H plans, gridCubeWeight T e H plans pin a) =
      ∑ a : GridAssignedTerm R r link H, gridAssignedWeight T e H pin a := by
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  refine Finset.sum_congr (Finset.ext fun _ => by simp) fun ext _ => ?_
  rw [Fintype.sum_sigma,Fintype.sum_sigma]
  refine Finset.sum_congr (Finset.ext fun _ => by simp) fun i _ => ?_
  exact ((plans i).value_eq_sum (H.term i).2 (historyPorts T e pin ext)).symm

/-- The field contraction equals the sum of the *post*-cube terms, each with
its real choices of selector and its own private and cube wire assignments. -/
theorem field_contraction_eq_grid_cube_terms
    (B : ValuedPack F D (fun _ : Fin r × Fin (publicWidth T) => 1))
    (pin : Fin d → Bool)
    (computes : ∀ ext team, B.tensor (fun p _ => publicBits T team pin ext p) = fieldValue T F pin ext team)
    (expand : ∀ ports, (unshortened B b K h).tensor ports = ∑ i, (H.term i).tensor ports) :
    fieldContraction T F pin = ∑ a : GridCubeTerm R r link H plans, gridCubeWeight T e H plans pin a :=
  (field_contraction_eq_grid_assignments T e H B pin computes expand).trans
    (sum_gridCubeWeight T e H plans pin).symm

end FinitePrewire

end BorderVNP
end Computability
end OAI
