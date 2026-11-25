import OAI.Computability.BorderVNP.PackedInheritedExtent
import OAI.Computability.BorderVNP.FiniteSewnFieldStaging
import OAI.Computability.BorderVNP.PackedInheritedWorkPrepCost

/-! # Recomputing the site extent after sewing and grouping the external ports

The previous terminal site's complete extent becomes the new private prefix.
The grouped layout supplies the new incident cable and port area. The gates
below share the previous assignment and scan the updated sparse endpoints.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing CellAddressCircuit CellAddressPhysical ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical
set_option maxHeartbeats 900000

variable {s m n C d k w : ℕ} {σ τ : Type} [Fintype σ] [Fintype τ]
variable (F : Fields s m n C d k w σ) (source : Frame τ σ)

private noncomputable abbrev oldExtent := Frame.initial fun z : Fin s × Fin w => F.auxWidth z.1 z.2

/-- The stored old extent and the live singleton incidence sum of the newly
sewn network feed a binary adder at each sparse site row. -/
noncomputable def sewnExtent : Frame τ (Fin s × Fin w) :=
  (exists_extent F (oldExtent F)).choose.subst source

/-- One pass through the source plus the actual sparse scan and the word additions. -/
theorem sewnExtent_size : (sewnExtent F source).size ≤
    source.size+(Views.frame F).size+1+s*3*(100*(w+1)^2) := by
  let ext := (exists_extent F (oldExtent F)).choose
  have bound : ext.size ≤ (oldExtent F).size+(Views.frame F).size+1+s*3*(100*(w+1)^2) :=
    (exists_extent F (oldExtent F)).choose_spec.1
  have small : ext.size ≤ (Views.frame F).size+1+s*3*(100*(w+1)^2) :=
    bound.trans_eq (by rw [show (oldExtent F).size=0 from rfl,Nat.zero_add])
  exact (Frame.subst_size ext source).le.trans ((Nat.add_le_add_left small source.size).trans_eq (by ac_rfl))

/-- At the processor's common word width this extra pass is sparse-linear
with a cubic word-arithmetic overhead. -/
theorem sewnExtent_cubic (F : Fields s m n C w k w σ) {R W : ℕ} (rows : 1+count s m n s ≤ R)
    (width : w ≤ W) (depth : Nat.clog 2 R ≤ W) :
    (sewnExtent F source).size ≤ source.size+4000*R*(W+1)^3 := by
  have size := sewnExtent_size F source
  have view := Views.frame_size F
  have cost := Prep.charge_cubic rows width depth
  unfold Prep.charge at cost
  omega

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable (cell : N.Site → Fin C) (state : N.Site → Site)
variable (runs : N.Site → List SewnField.Interval) (x : τ → Bool)

/-- The original saved word at each site and the true post-sewing pointers
suffice for the extent of the adapted site program. Vacant rows stay zero. -/
theorem sewnExtent_covers (rep : Represents N cell (fun v => (state v).size) siteID edgeID portID F (source.eval x))
    (room : ∀ v, (state v).size + incoming N v < 2^w) :
    Covers siteID (fun v => (SewnField.stage (state v) (incoming N v) (runs v)).size) (sewnExtent F source) x := by
  let adapt := fun v => SewnField.stage (state v) (incoming N v) (runs v)
  have previous : Covers siteID (fun v => (adapt v).work) (oldExtent F) (source.eval x) := by
    constructor
    · intro v
      simpa only [oldExtent,Frame.initial_eval,Function.comp_def,SewnField.stage,adapt] using rep.stage v
    · intro i hi
      simpa only [oldExtent,Frame.initial_eval,Function.comp_def] using rep.stageHole i hi
  have read := extent_covers N F siteID edgeID portID (oldExtent F) (Views.EndpointData.of_rep N F siteID edgeID portID rep)
    adapt (fun _ => rfl) previous room (exists_extent F (oldExtent F)).choose ((exists_extent F (oldExtent F)).choose_spec.2 _)
  constructor
  · intro v; simpa only [sewnExtent,Frame.subst_eval] using read.live v
  · intro i hi; simpa only [sewnExtent,Frame.subst_eval] using read.hole i hi

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
