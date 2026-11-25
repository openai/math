import OAI.Hierarchy.ProbeFixedNativeBoards

namespace OAI
/-! # The two catalyst reads of the mounted fixed program -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard StripDirectory StripChart CatalogueRows
open scoped Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {z raw : ℕ}
local notation "N" => Stages z (2^v.W)
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))

/-- The emitted pair decodes the mounted role and ball and addresses the radius
port on the located board. This holds for every input board and attempt. -/
theorem physicalTrees_mounted_header (origin : Boards z (2^v.W) k raw v.depth)
    (P : v.Placement) (width : ℕ) (a : Attempt) :
    let H := StripChart.header F (v.mounted origin P width) a
    let radius := radiusMate (v.located origin P width) v.mesh P.catalogue P.routes a
    let flag := catalystFlag (z:=z) (W:=v.W) (k:=k) (depth:=v.depth) a
    (v.physicalTrees origin P width a).catalystMate =
      some (chooseField D 0 flag H.fieldTerm,
        P.catalogue.checkedEdge (chooseField D 0 (fun i => (radius i).atRow H.ballTerm) H.fieldTerm)) := rfl

private theorem reserve_header {u d k₀ letters depth : ℕ} (F : Type*) [Field F]
    [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages u d)) k₀)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k₀)]
    (s : Boards u d k₀ letters depth) (c : Mesh) (A : Arena) (initial : ℕ)
    (empty : Bank) (a : Attempt) :
    StripChart.header F (withReserveSource F s c A initial empty) a = StripChart.header F s a := by
  cases a <;> rfl

/-- The seeded native caller reads the same two words from its installed
occurrence header after the reserve source has been attached. -/
theorem nativeTrees_mounted_header (P : v.Placement) (z width : ℕ) (a : Attempt) :
    let H := StripChart.header F (v.nativeBoards P z width) a
    let radius := radiusMate (v.located (v.seed P z width) P width) v.mesh P.catalogue P.routes a
    let flag := catalystFlag (z:=z) (W:=v.W) (k:=k) (depth:=v.depth) a
    (v.nativeTrees P z width a).catalystMate =
      some (chooseField _ 0 flag H.fieldTerm,
        P.catalogue.checkedEdge (chooseField _ 0 (fun i => (radius i).atRow H.ballTerm) H.fieldTerm)) := by
  have directory : StripChart.header F (v.nativeBoards P z width) a =
      StripChart.header F (v.mounted (v.seed P z width) P width) a :=
    reserve_header F (v.mounted (v.seed P z width) P width) v.mesh (v.privateArena P z width)
      P.joint.initial (v.emptyReserve P z width) a
  rw [directory]
  exact v.physicalTrees_mounted_header (v.seed P z width) P width a

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
