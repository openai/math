import OAI.Computability.BorderVNP.FinitePrewireGrid

/-! # Assigned terms after the interior-wired finite-field substitution

Only the exterior bits are independent of the packed history. All original
within-team variables already occur inside the private cells. The remaining
indices of a shortened term are its actual history and its internal wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FinitePrewire

open Crossing Packing Shortening ParseBatch.Prewire TeamContraction FieldTeam FiniteDiagonal
open scoped BigOperators Classical

variable {D R r t d link inner n b K h : ℕ} {Edge : Type} [Fintype Edge]
    (T : Wiring R r t d link inner n Edge) {F : Type*} [Field F] [Fintype F]
    (e : PackPorts Unit b K h ≃ Fin (R+1))

/-- The visible inputs of each assigned term are supplied by the shared
exterior assignment and the processor fields at the fixed pin. -/
def historyPorts (pin : Fin d → Bool) (ext : Exterior R r link → Bool) :
    Ports (packWidth (fun _ : Fin r × Fin (publicWidth T) => 1) b K h) :=
  packInputs b K h (fun u p _ => publicBits T (e u) pin ext p)

/-- The public exterior assignment, the selected actual packed history and its
internal cables. The initial private edge assignments have already been summed. -/
abbrev GridAssignedTerm (R r link : ℕ) {P : Type} {bits : P → ℕ}
    (H : ProfileSum (ValuedPack F D bits)) :=
  (Exterior R r link → Bool) × (i : H.Index) × (H.term i).1.Assignment

variable (H : ProfileSum (ValuedPack F D (packWidth (fun _ : Fin r × Fin (publicWidth T) => 1) b K h)))

/-- The product of the actual local tables at the selected private assignment. -/
noncomputable def gridAssignedWeight (pin : Fin d → Bool) (a : GridAssignedTerm R r link H) : F :=
  let p := H.term a.2.1
  ∏ v, p.1.read p.2 a.2.2 (historyPorts T e pin a.1) v

/-- The full live field contraction equals the sum of the assigned adaptive
terms of the prewired grid. Exterior links are counted once and no separate
interior assignment appears outside the contracted team tables. -/
theorem field_contraction_eq_grid_assignments
    (M : ValuedPack F D (fun _ : Fin r × Fin (publicWidth T) => 1))
    (pin : Fin d → Bool)
    (computes : ∀ ext team, M.tensor (fun p _ => publicBits T team pin ext p) = fieldValue T F pin ext team)
    (expand : ∀ ports, (unshortened M b K h).tensor ports = ∑ i, (H.term i).tensor ports) :
    fieldContraction T F pin = ∑ a : GridAssignedTerm R r link H, gridAssignedWeight T e H pin a := by
  rw [fieldContraction_eq,Fintype.sum_prod_type]
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro ext _
  trans (unshortened M b K h).tensor (historyPorts T e pin ext)
  · rw [unshortened_copies,historyPorts]
    simp only [copyPorts_packInputs, computes]
    exact (e.prod_comp (fieldValue T F pin ext)).symm
  · rw [expand,Fintype.sum_sigma]
    apply Finset.sum_congr (Finset.ext fun _ => by simp)
    intro i _
    unfold Pack.tensor Network.value gridAssignedWeight
    apply Finset.sum_congr (Finset.ext fun _ => by simp)
    intro a _
    exact Finset.prod_congr (Finset.ext fun _ => by simp) fun _ _ => rfl

end FinitePrewire

end BorderVNP
end Computability
end OAI
