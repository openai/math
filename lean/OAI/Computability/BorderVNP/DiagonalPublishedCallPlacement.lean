import OAI.Computability.BorderVNP.DiagonalReceivedCoreTerminal
import OAI.Computability.BorderVNP.FiniteEvaluatorReturnedTerminalOperands

/-! # Actual sparse placement at every selected global ordinal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing Packing.Inherited CellSparse DiagonalTallyCellReports RoutingISA
open CellPacketGeometry CellPacketGeometry.SiteWords CellPacketGeometry.History CellPacketGeometry.History.Native
open CellSparse.Packet CellSparse.Packet.Source RoutingISA.CellPacket

variable {D n d blocks b h K teams slots : ℕ} {P Orig E : Type} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} (B : CoreDirectory N n d blocks b h K teams)

/-- Read the returned directory at exactly the total global lookup used by the
sparse producer. The published start and stop markers supplied by the native
geometry are the addresses of the same placed packet. -/
theorem CoreDirectory.nativeCallPlacement
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
          (fun v => (B.programs v).program) c.val (geometry.reports c.castSucc))
    (hf : B.cells+1+geometry.words.length+(B.cells+1)≤2^p)
    (hs : B.cells+1+(Schema.coords (geometry.referenceRows ptr).length).length+(B.cells+1)≤2^chunk)
    (c : Fin B.cells) :
    let rows := atRanges (dest:=dest) (H:=header) geometry ptr hf hs ram slot fs ext scratch burst bytes
    let pl := Terminal.placeAt rows c.val
    CellMemory pl (pl.publicBase+((Supplement.prefixParts pl).flatMap Part.publicBuffer).length)
        (descriptorBank dest p+ram (descriptorBank dest p+(2^chunk+(Markers.stop hs c.castSucc).val))) ram ∧
    pl.directory=FinalCell.directory parsedOwner N (fun v => (B.cell v).val) B.siteID B.edgeID B.portID
      (fun v => (B.programs v).program) c.val (countFields
        (FinalCell.countBase N (fun v => (B.cell v).val) (fun v => (B.programs v).program) c.val)
        layout.gadgets layout.countWidth) ∧
    pl.privateWires=FinalCell.privateBits N (fun v => (B.cell v).val) (fun v => (B.programs v).program) c.val := by
  intro rows pl
  obtain ⟨_,_,read,shape⟩ := B.nativePublishedRows geometry ptr args ram publication slot fs ext scratch burst bytes
    address parsedOwner publishedOwner occupied layout returned
  have same : pl = rows c.castSucc := congrArg rows (Fin.ext (Nat.min_eq_left c.isLt.le))
  rw [same]
  exact ⟨read _,shape c⟩

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
