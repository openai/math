import OAI.Computability.BorderVNP.DiagonalCandidateOriginalPublication
import OAI.Computability.BorderVNP.DiagonalSignedCommonPlacement
import OAI.Computability.BorderVNP.PackedNativeDemandRows

/-! # The actual directory publication underlying a candidate's argument window -/

namespace OAI
namespace Computability
namespace BorderVNP

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


variable {R X : ℕ} {word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap}
    {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration task.cube.n task.cube.header.d}
    {group : Fin task.cube.header.d → Fin (R+1)} {guess : ℕ → Bool}
local notation3 (prettyPrint := false) "regPP" => NativeDemands.privatePair N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "regLP" => NativeDemands.livePair N cell edgeID portID dir original live gap
variable {I A : Type} [Fintype I] {host : I → Fin task.cube.cells} {keys : I ↪ ℕ} {sizes : I → ℕ}
    {recv : A → Fin task.cube.cells} {amount : A → ℕ}
    (site : SignedPrep.CandidateSite (X:=X) task.cube dir
      (NativeDemands.privatePair N cell edgeID portID dir original live gap)
      (NativeDemands.livePair N cell edgeID portID dir original live gap) word owner decl group a.frame a.next
      (a.operands u slot packet).layout fields f guess pub mac postPin pinMem host keys sizes N cell recv amount)
local notation3 (prettyPrint := false) "pr" => privateLayout a.frame origin task.cube.cables task.cube.cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tabs" => bases origin task.cube.cables task.cube.cells dir.entries
local notation3 (prettyPrint := false) "actualPP" => ISA.placement (readings site.middle) (pr).raw
local notation3 (prettyPrint := false) "actualLP" => ISA.placement (readings site.middle) (tabs).livePairs
local notation3 (prettyPrint := false) "nativeHost" => Sum.elim
  (Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin task.cube.cells → Fin task.cube.cells)) (cell ∘ original)
local notation3 (prettyPrint := false) "nativeKey" => numbered (reserveID (C:=task.cube.cells) (suppliedID N cell edgeID portID))
local notation3 (prettyPrint := false) "nativeSizes" => Sum.elim
  (Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)) (fun _ => dir.description)

private theorem publication_congr {w : ℕ} (middle output : Memory w) (frame base : ℕ)
    {first second : List Directory.Row} (actual : output=ISA.publish middle frame base first)
    (same : first=second) : output=ISA.publish middle frame base second :=
  actual.trans (congrArg (ISA.publish middle frame base) same)

set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-- On the candidate's actual epoch return, the canonical raw-row guard can be
read on the two physical placement tables. The writer that is about to run
starts at exactly the resulting native directory, with its real input and
output pointer. -/
theorem PublishedPin.candidate_argument_publication {s cuts ownerWidth fieldWidth : ℕ}
    {σ : Type} [Fintype σ] (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    (geometry : Fields s task.cube.cables p task.cube.cells cuts ownerWidth fieldWidth σ)
    (x : σ → Bool) (net : CellAddressPhysical.Represents N cell aux siteID edgeID portID geometry x)
    (numbers : ∀ c, (geometry.cells c).val=c.val)
    (room : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^fieldWidth)
    (bounds : dir.DestinationBounds) (width : ∀ i,bits (live i)=dir.block)
    (image : Image geometry (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings site.geometry))
    (sources : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields
      pub mac v postPin pinMem site.geometryRegs site.geometry site.used site.profileCost) :
    let mid := site.middle
    let pp := actualPP
    let lp := actualLP
    (pr).Image (readings site.geometry) dir.entries (readings mid) ∧ (pr).Fits w (readings site.geometry) ∧
      Nonempty (SlottedWriter task.cube dir pp lp (a.operands u slot packet).layout pub mid a.next nativeHost nativeKey nativeSizes) ∧
      SignedPrep.PinnedRawInput (ar:=task.cube) (D:=dir) (pp:=pp) (lp:=lp) (pub:=pub) (slotted:=mid) (base:=a.next)
        f site.old site.fresh site.gates site.outputs site.width site.off site.ell site.control site.profile site.claims site.pad word R X ∧
      site.published.val.2.2=ISA.publish mid (pub 0).val a.next (dir.directory pp lp) ∧
      DataReady pub site.receipt.history.dataInput ∧
        (RoutingISA.Transmission.DataWriter.layout (readings pub) (readings site.receipt.history.dataInput)).output=task.cube.records := by
  intro mid pp lp
  obtain ⟨placed,fit,writer⟩ := PublishedPin.candidate_geometry task dir N cell edgeID portID original live
    a u slot packet origin gap f hdr fields pub mac v postPin pinMem site sources
  have stored := NativeDemands.rows_eq_native N cell edgeID portID dir original live gap aux siteID geometry x a.frame
    origin (readings site.geometry) (readings mid) net numbers room bounds width image placed fit
  have equalRows : dir.directory regPP regLP=dir.directory pp lp := stored
  exact ⟨placed,fit,writer,site.input.commonPlacement (pp':=pp) (lp':=lp) equalRows,
    publication_congr mid site.published.val.2.2 (pub 0).val a.next site.actual equalRows,
    site.receipt.done.emission.demand.ready,site.receipt.done.emission.demand.records⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
