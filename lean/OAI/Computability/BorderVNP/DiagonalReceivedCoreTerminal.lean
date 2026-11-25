import OAI.Computability.BorderVNP.DiagonalReceivedCoreSound
import OAI.Computability.BorderVNP.DiagonalNativeTerminalCell
import OAI.Computability.BorderVNP.CellPacketGeometrySignedPlacements

/-! # The published cell directory and the source used by the signed path decoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing Packing.Inherited CellSparse DiagonalTallyCellReports RoutingISA
open CellPacketGeometry CellPacketGeometry.SiteWords CellPacketGeometry.History CellSparse.Packet
open RoutingISA.CompactMachine SparseExterior

variable {D n d blocks b h K teams slots : ℕ} {P Orig : Type} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} (B : CoreDirectory N n d blocks b h K teams)
    (geometry : SiteWords.Directory (Fin slots) Orig (B.cells+1)) (fs : Orig → List Factor)
    (header : ℕ) (places : Fin (B.cells+1) → CellPacket.Placed Orig)
    (shape : TypedBatch.SourceShape places geometry) (parsedOwner publishedOwner : Fin B.siteRows → ℕ)
    (occupied : ∀ v, parsedOwner (B.siteID v)=publishedOwner (B.siteID v))
    (layout : ReportLayout) (c : Fin B.cells)

local notation3 (prettyPrint := false) "sites" => fun v => (B.programs v).program
local notation3 (prettyPrint := false) "home" => fun v => (B.cell v).val
local notation3 (prettyPrint := false) "counts" => countFields (FinalCell.countBase N home sites c.val) layout.gadgets layout.countWidth

include shape occupied
/-- Private wiring and the whole sorted sparse directory of a genuine cell of
the returned placement. The floor between the used cells and the spare row is
the same one used by the native ownership scan. -/
theorem CoreDirectory.placedAtReceivedCell
    (body : (places c.castSucc).factors = fs)
    (wires : geometry.privateWires c.castSucc = FinalCell.privateBits N home sites c.val)
    (reported : geometry.reports c.castSucc = counts)
    (published : ((geometry.placed c.castSucc header (fun _ => 0) fs 0 0 0 0 0 []).directory) =
      FinalCell.directory publishedOwner N home B.siteID B.edgeID B.portID sites c.val (geometry.reports c.castSucc))
    : (places c.castSucc).directory = FinalCell.directory parsedOwner N home B.siteID B.edgeID B.portID sites c.val counts ∧
      (places c.castSucc).privateWires=FinalCell.privateBits N home sites c.val := by
  let placed := places c.castSucc
  have emitted : placed.directory=(geometry.placed c.castSucc header (fun _ => 0) fs 0 0 0 0 0 []).directory := by
    change CellSparse.Directory.mk (placed.boxes.map (Source.factors placed.factors)) placed.rows placed.reports =
      CellSparse.Directory.mk ((geometry.cellBoxes c.castSucc).map (Source.factors fs)) (geometry.cellRecords c.castSucc)
        (geometry.reports c.castSucc)
    simp only [placed,shape.boxes,shape.records,shape.reports,body]
  have merged := emitted.trans published
  rw [reported] at merged
  have owners := FinalCell.directory_congr_occupied N home B.siteID B.edgeID B.portID sites
    parsedOwner publishedOwner occupied c.val counts
  exact ⟨merged.trans owners.symm,(shape.privateWires c.castSucc).trans wires⟩

/-- Read a real cell of the published terminal (before the spare row) on its
native allocation. Only occupied site ordinals affect the directory; guessed
subtotal and use bits can be arbitrary. -/
theorem CoreDirectory.logicalReceivedCell
    (body : (places c.castSucc).factors = fs)
    (wires : geometry.privateWires c.castSucc = FinalCell.privateBits N home sites c.val)
    (reported : geometry.reports c.castSucc = counts)
    (published : ((geometry.placed c.castSucc header (fun _ => 0) fs 0 0 0 0 0 []).directory) =
      FinalCell.directory publishedOwner N home B.siteID B.edgeID B.portID sites c.val (geometry.reports c.castSucc))
    (report : ReportCell layout) (cursor : LocalReportCursor) (field : Field) (supply : List Bool)
    (bytes : field.values=supply++report.bits) :
    logicalCell (places c.castSucc) (bindingRows report.bundles cursor) field =
      FinalCell.withWiring (FinalCell.cellInput N home B.siteID B.edgeID B.portID parsedOwner sites c.val
        layout.gadgets layout.countWidth (supply++report.bits)) (bindingRows report.bundles cursor) := by
  obtain ⟨live,pw⟩ := B.placedAtReceivedCell geometry fs header places shape parsedOwner publishedOwner occupied layout c
    body wires reported published
  change CellInput.mk (BottomReports.appendRows (places c.castSucc).directory _) (places c.castSucc).privateWires field.values = _
  rw [live,pw,bytes]
  rfl

end Cube.Physical.NativeAssignments

namespace Cube.Physical.NativeAssignments

open Crossing Packing Packing.Inherited CellSparse DiagonalTallyCellReports RoutingISA
open CellPacketGeometry CellPacketGeometry.SiteWords CellPacketGeometry.History CellPacketGeometry.History.Native
open CellSparse.Packet CellSparse.Packet.Source RoutingISA.CellPacket

variable {D n d blocks b h K teams slots : ℕ} {P Orig E : Type} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} (B : CoreDirectory N n d blocks b h K teams)

/-- A true native geometry publication yields one common pair of marker tables
for all owned cells. For every genuine cell the directory and width agree with
the signed core used by the path decoder, on this same reached memory. -/
theorem CoreDirectory.nativePublishedRows
    (geometry : SiteWords.Directory (Fin slots) Orig (B.cells+1)) {p chunk dest header : ℕ}
    (ptr : Orig → E) (args : E → ℕ) (ram : ℕ → ℕ) (publication : Published geometry p chunk dest header ptr args ram)
    (slot : Orig → ℕ) (fs : Orig → List Factor) (ext scratch burst : Fin (B.cells+1) → ℕ)
    (bytes : Fin (B.cells+1) → List Bool) (address : ∀ i, args (ptr i)=slot i)
    (parsedOwner publishedOwner : Fin B.siteRows → ℕ)
    (occupied : ∀ v, parsedOwner (B.siteID v)=publishedOwner (B.siteID v))
    (layout : ReportLayout)
    (returned : ∀ c : Fin B.cells,
      (geometry.privateWires c.castSucc=FinalCell.privateBits N (fun v => (B.cell v).val) (fun v => (B.programs v).program) c.val ∧
        geometry.reports c.castSucc=countFields (FinalCell.countBase N (fun v => (B.cell v).val)
          (fun v => (B.programs v).program) c.val) layout.gadgets layout.countWidth) ∧
      ∀ addr pb db eb sc bu bs, (geometry.placed c.castSucc header addr fs pb db eb sc bu bs).directory =
        FinalCell.directory publishedOwner N (fun v => (B.cell v).val) B.siteID B.edgeID B.portID
          (fun v => (B.programs v).program) c.val (geometry.reports c.castSucc)) :
    ∃ hf : B.cells+1+geometry.words.length+(B.cells+1)≤2^p,
    ∃ hs : B.cells+1+(Schema.coords (geometry.referenceRows ptr).length).length+(B.cells+1)≤2^chunk,
      let places := atRanges (dest := dest) (H := header) geometry ptr hf hs ram slot fs ext scratch burst bytes
      (∀ c, CellMemory (places c) ((places c).publicBase+((Supplement.prefixParts (places c)).flatMap Part.publicBuffer).length)
        (descriptorBank dest p+ram (descriptorBank dest p+(2^chunk+(Markers.stop hs c).val))) ram) ∧
      ∀ c : Fin B.cells,
        (places c.castSucc).directory = FinalCell.directory parsedOwner N (fun v => (B.cell v).val) B.siteID B.edgeID B.portID
          (fun v => (B.programs v).program) c.val (countFields
            (FinalCell.countBase N (fun v => (B.cell v).val) (fun v => (B.programs v).program) c.val) layout.gadgets layout.countWidth) ∧
        (places c.castSucc).privateWires = FinalCell.privateBits N (fun v => (B.cell v).val) (fun v => (B.programs v).program) c.val := by
  obtain ⟨hf,hs,shape,mem⟩ := publication.places geometry ptr ram slot fs ext scratch burst bytes address
  refine ⟨hf,hs,mem,fun c => ?_⟩
  exact B.placedAtReceivedCell geometry fs header _ shape parsedOwner publishedOwner occupied layout c rfl
    (returned c).1.1 (returned c).1.2 ((returned c).2 (fun _ => 0) 0 0 0 0 0 [])

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
