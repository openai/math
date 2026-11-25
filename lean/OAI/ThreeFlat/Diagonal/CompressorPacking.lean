import OAI.ThreeFlat.Diagonal.CompressorTags
import OAI.Computability.VPVNP.BitSlotIndex
import Mathlib.Data.Fintype.Pi

namespace OAI
/-! # Instantiating the shrinking layout on an actual lifted slot graph -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression
open scoped Classical
variable {V H Tag L : Type*} {d c : ℕ}

/-- Move the tag and remaining lane into the site label before assigning the
old arcs to motifs. -/
def packedAddress : ((V × Fin d) × (BitWord c × H × Tag × L)) ≃ Arc V H Tag L d c where
  toFun z := (((z.1.1,z.2.2.2),z.1.2),z.2.1,z.2.2.1)
  invFun z := ((z.1.1.1,z.1.2),z.2.1,z.2.2,z.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] [Fintype V] [Fintype Tag]

/-- A graph with the prescribed split lane coordinates admits the packing
data. Slots and displacements are the ones used by the input graph. -/
noncomputable def packingData (G : LiftedSlots V d (BitWord (2*d+1) × H × Tag × L))
    (slots : H ≃ Fin d) (size : 2*d*((d+1)+(d+1)^2) < Fintype.card Tag) :
    PackingData V H Tag L d (2*d+1) where
  slots := G.base
  color := (proper_coloring G.base).choose
  proper := (proper_coloring G.base).choose_spec
  slotLabel := slots
  offset := (exists_offsets G.base (fun e => (G.displacement e).2.2.1) size).choose
  bitShift e := (G.displacement e).1
  slotShift e := (G.displacement e).2.1
  siteShift e := (G.displacement e).2.2

omit [AddCommGroup H] [AddCommGroup L] in
theorem packing_conditions (G : LiftedSlots V d (BitWord (2*d+1) × H × Tag × L))
    (slots : H ≃ Fin d) (size : 2*d*((d+1)+(d+1)^2) < Fintype.card Tag) :
    TagConditions G.base (fun e => (G.displacement e).2.2.1) (packingData G slots size).offset :=
  (exists_offsets G.base _ size).choose_spec

/-- Grouping coordinates in the packed address transports the original
slot permutation, so all thick and thin counts refer to its actual arcs. -/
theorem packing_actual (G : LiftedSlots V d (BitWord (2*d+1) × H × Tag × L))
    (slots : H ≃ Fin d) (size : 2*d*((d+1)+(d+1)^2) < Fintype.card Tag)
    (z : (V × Fin d) × (BitWord (2*d+1) × H × Tag × L)) :
    (packingData G slots size).actual (packedAddress z) = packedAddress (G.actualTarget z) := rfl

omit [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] in
theorem position_count [Fintype H] [Fintype L] (P : PackingData V H Tag L d c) :
    Fintype.card (Position V H Tag L c) = Fintype.card (Site V Tag L) * (2 ^ c * d) := by
  change Fintype.card (Site V Tag L × (BitWord c × H)) = _
  rw [Fintype.card_prod, Fintype.card_prod (α := BitWord c) (β := H),
    Fintype.card_congr P.slotLabel,Fintype.card_fin]
  simp [BitWord]

end ThreeFlat.Diagonal.CompressorPacking

end OAI
