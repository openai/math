import OAI.Computability.BorderVNP.DiagonalSignedCandidateSite
import OAI.Computability.BorderVNP.DiagonalPublishedCanonicalHost
import OAI.Computability.BorderVNP.DiagonalReportSourcePlacement

/-! # The canonical host directory on a candidate's original returned pin -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Packing.Directory Packing.Directory.PrivateBank LocalRow BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex
open scoped Classical

open CellMacro.Generator RoutingISA.CompactMachine PackedHistoryCircuit

variable {D p w d g : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (task : SignedTaskArena.Layout) (dir : Directory.Layout) (N : Network D P bits)
    (cell : N.Site → Fin task.cube.cells) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (packet : ReferencePacket w d) (origin gap : ℕ)
    (f : BroadcastFrame) (hdr : List Bool) (fields : Pins.ProcessorFields (a.operands u slot packet).layout)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (v : Fin g → Bool)
    (postPin : Bank w) (pinMem : Memory w)

variable {R X baseFrame : ℕ} {pp lp : ℕ → ℕ × ℕ} {word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap}
    {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration task.cube.n task.cube.header.d}
    {group : Fin task.cube.header.d → Fin (R+1)} {guesses : ℕ → Bool}
    {I A : Type} [Fintype I] {host : I → Fin task.cube.cells} {ids : I ↪ ℕ} {size : I → ℕ}
    {recv : A → Fin task.cube.cells} {amount : A → ℕ}
    (site : SignedPrep.CandidateSite (X:=X) task.cube dir pp lp word owner decl group baseFrame a.next
      (a.operands u slot packet).layout fields f guesses pub mac postPin pinMem host ids size N cell recv amount)

local notation3 (prettyPrint := false) "pr" => privateLayout a.frame origin task.cube.cables task.cube.cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tabs" => bases origin task.cube.cables task.cube.cells dir.entries

variable {task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields pub mac v postPin pinMem}

local notation3 (prettyPrint := false) "canonP" => NativeDemands.privatePair N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "canonL" => NativeDemands.livePair N cell edgeID portID dir original live gap

/-- The two placement tables on this site's real middle RAM agree at all
occupied keys with the original semantic operands. The publisher and its
writer therefore realize the semantic directory on that same return, and
its report words transfer with their original addresses and sign. -/
theorem PublishedPin.candidateCanonicalEntry
    (pin : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields
      pub mac v postPin pinMem site.geometryRegs site.geometry site.used site.profileCost)
    {ns cb lb wb : ℕ} {σ : Type} [Fintype σ] (aux : N.Site → ℕ) (ids : N.Site ↪ Fin ns)
    (geom : Fields ns task.cube.cables p task.cube.cells cb lb wb σ) (x : σ → Bool)
    (rep : Packing.CellAddressPhysical.Represents N cell aux ids edgeID portID geom x) (cells : ∀ c,(geom.cells c).val=c.val)
    (width : ∀ j,bits (live j)=dir.block)
    (small : ∀ c,guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^wb)
    (image : Image geom (ids ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings site.geometry))
    (bounds : dir.DestinationBounds) :
    let raw := Directory.ISA.placement (readings site.middle) (pr).raw
    let resident := Directory.ISA.placement (readings site.middle) (tabs).livePairs
    (∀ j,dir.keyPlacement raw resident j=dir.keyPlacement canonP canonL j) ∧
      site.published.val.2.2=Directory.ISA.publish site.middle a.frame a.next (dir.directory canonP canonL) ∧
      Nonempty (SlottedWriter task.cube dir canonP canonL (a.operands u slot packet).layout pub site.middle a.next
        (Sum.elim (Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin task.cube.cells → Fin task.cube.cells))
          (cell ∘ original)) (numbered (reserveID (C:=task.cube.cells) (suppliedID N cell edgeID portID)))
        (Sum.elim (Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)) (fun _ => dir.description))) ∧
      ∀ (head : ℕ) (written result : ℕ → ℕ) (signed : Bool),
        SignedTaskArena.ReportWords task head (readings (Directory.ISA.publish site.middle head a.next
          (dir.directory raw resident))) written result signed →
          SignedTaskArena.ReportWords task head (readings (Directory.ISA.publish site.middle head a.next
            (dir.directory canonP canonL))) written result signed := by
  intro raw resident
  have physical := pin.canonicalSlottedReturn task dir N cell edgeID portID original live a u slot packet
    origin gap f hdr fields pub mac v postPin pinMem site.geometryRegs site.geometry site.used site.profileCost
    site.epoch site.published aux ids geom x rep cells width small image bounds
  obtain ⟨keys,actual,writer⟩ := physical
  have occupied : ∀ j,dir.keyPlacement raw resident j=dir.keyPlacement canonP canonL j := by
    simpa only [site.epochMemory] using keys
  refine ⟨occupied,?_,?_,fun _ _ _ _ words => words.withKeyPlacements bounds occupied⟩
  · simpa only [site.epochMemory] using actual
  · simpa only [site.epochMemory] using writer

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
