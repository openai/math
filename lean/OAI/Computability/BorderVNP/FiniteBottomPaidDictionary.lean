import OAI.Computability.BorderVNP.FiniteBottomGridLocality
import OAI.Computability.BorderVNP.PackedHistoryPrivateModels

/-! # One field dictionary for original and paid factors in a physical history

Fine rows and paid factors use their true field-element codes. Equal
scalars share one tally position. The one dictionary used by the finite
field processor realizes the initial programs and all later paid births.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.FiniteBottom

open Crossing Shortening Inherited BottomGridBank
open scoped Classical

variable (F : Type*) [Field F] [Fintype F] {E : Type*}

/-- The real finite tally slot for a paid identity entry. Equal field values
use the same position throughout the history. -/
noncomputable def scalarPaidCode (paid : E → F) (t : E) : ℕ := (Fintype.equivFin F (paid t)).val

/-- The finite scanner's dictionary returns the true paid value. -/
theorem scalarPaidCode_value (paid : E → F) (t : E) : scalarValue F (scalarPaidCode F paid t) = paid t :=
  scalarValue_code (paid t)

omit [Field F] in
/-- Every paid table row lies inside the actual field processor's report vector. -/
theorem scalarPaidCode_lt (paid : E → F) (t : E) : scalarPaidCode F paid t < Fintype.card F :=
  (Fintype.equivFin F (paid t)).isLt

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa)
variable (T : N.Tables F) (copies capFine : ℕ) (fit : ∀ v, GridBoxes.stride N cell v ≤ capFine)

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "birth" => finiteBorn N cell position pack width owner lane aligned siteID edgeID portID channelID groupID

/-- The genuine bottom pack at the input of a normalized history. -/
noncomputable abbrev bottomPack : Pack D A (fun a => copies*width a) F :=
  ⟨BottomRepeat.wide G copies,repeatedTable N cell position pack width owner lane aligned T copies⟩

/-- The private lineages begin at the actual sparse field directories and
carry their concrete incidence sizes. -/
noncomputable def bottomPrograms : Site.Programs (BottomRepeat.wide G copies) :=
  fun v => Site.Lineage.start (birth v T copies capFine (fit v)) rfl

/-- Every bottom lineage satisfies the joint field invariant used by the
stage installation theorem, with all original and paid codes realized. -/
theorem bottomPrograms_models :
    Site.Programs.FieldModels (bottomPack F N cell position pack width owner lane aligned T copies)
      channelID groupID (bottomPrograms F N cell position pack width owner lane aligned siteID edgeID portID
        channelID groupID T copies capFine fit) (scalarValue F) := fun v =>
  ⟨finiteBorn_local N cell position pack width owner lane aligned siteID edgeID portID channelID groupID
      v T copies capFine (fit v),
    finiteBorn_models N cell position pack width owner lane aligned siteID edgeID portID channelID groupID
      v T copies capFine (fit v)⟩

end Packing.FiniteBottom

end BorderVNP
end Computability
end OAI
