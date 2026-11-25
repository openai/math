import OAI.Computability.BorderVNP.PackedCellAddressPhysical
import OAI.Computability.BorderVNP.PackedProfileCounts
import OAI.Computability.BorderVNP.DiagonalExternalSewFieldFrame

/-! # Publishing narrow history widths alongside wider geometry controls

The original route and private-program widths remain on the history's own
word wires. The geometry emitter can use a larger word for cell addresses,
task controls and packet offsets by connecting high-order bits to its
already available false input. Cell and site IDs keep their original keys.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddressCircuit

open Crossing CellAddressPhysical ParseBatchSort VPVNP.VerifierNetwork Diagonal.ExternalSew.FieldExport
open private extend extend_value extend_map from OAI.Computability.BorderVNP.PackedProfileCounts

variable {σ : Type*} {s m n C d k w b : ℕ} (F : Fields s m n C d k w σ)

/-- Zero-extend an unsigned MSB-first word by connecting existing pins. -/
def widthPins (h : w≤b) (zero : σ) (a : Fin w → σ) (j : Fin b) : σ :=
  extend zero a (b-w) (Fin.cast (by omega) j)

/-- The integer on the extended pins equals the original integer. -/
theorem widthPins_value (h : w≤b) (zero : σ) (a : Fin w → σ) (x : σ → Bool) (hz : x zero=false) :
    value (x ∘ widthPins h zero a) = value (x ∘ a) := by
  have atWidth (v : ℕ) (eq : b=w+v) :
      value (x ∘ fun j : Fin b => extend zero a v (Fin.cast eq j)) = value (x ∘ a) := by
    subst b
    change value (x ∘ extend zero a v) = _
    rw [extend_map,hz,extend_value]
  exact atWidth (b-w) (by omega)

/-- Width extension does not add gates to the public source. Site and cell
keys, pointers, and all attachment maps are forwarded directly. -/
def Fields.widenWidths (h : w≤b) (zero : σ) : Fields s m n C d k b σ :=
  { F with edgeWidth := fun e => widthPins h zero (F.edgeWidth e)
           auxWidth := fun v => widthPins h zero (F.auxWidth v)
           portWidth := fun p => widthPins h zero (F.portWidth p) }

variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (aux : N.Site → ℕ) (site : N.Site ↪ Fin s) (edge : N.Edge ↪ Fin m) (port : P ↪ Fin n)
    [Fintype σ]

omit [Fintype σ] in
/-- The same true network, staging sizes and sparse holes are represented
at the chosen external geometry width, including every unused pointer row. -/
theorem widened_represents (h : w≤b) (zero : σ) (x : σ → Bool) (hz : x zero=false)
    (rep : Represents N cell aux site edge port F x) :
    Represents N cell aux site edge port (F.widenWidths h zero) x := by
  refine ⟨rep.owner,rep.src,rep.dst,rep.attach,?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [Fields.widenWidths,widthPins_value h zero _ x hz]
  exacts [rep.edge,rep.stage,rep.port,rep.edgeHole,rep.stageHole,rep.portHole]

/-- The shared sewn source supplies the required false input automatically. -/
theorem sewn_widened_represents {γ : Type*} [Fintype γ] (B : Fields s m n C d k w (σ ⊕ Bool))
    (source : Frame γ σ) (y : γ → Bool) (h : w≤b)
    (rep : Represents N cell aux site edge port B ((withSewnFields source).eval y)) :
    Represents N cell aux site edge port (B.widenWidths h (.inr false)) ((withSewnFields source).eval y) := by
  apply widened_represents B N cell aux site edge port h (.inr false) _ _ rep
  simp only [withSewnFields,Frame.subst_eval,constants_eval,Sum.elim_inr,id_eq]

end Packing.CellAddressCircuit

end BorderVNP
end Computability
end OAI
