import OAI.Computability.BorderVNP.DiagonalSignedOwnedAddress
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsBundle
import OAI.Computability.BorderVNP.DiagonalFrozenPaddingControls
import OAI.Computability.BorderVNP.DiagonalPublishedHostCables
import OAI.Computability.BorderVNP.DiagonalSparseReportOrdinals
import OAI.Computability.BorderVNP.DiagonalCanonicalReportDirectory

/-! # The full original marked site at the actual owned host scatter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator
open private detOfUnsigned from OAI.Computability.BorderVNP.CubeISALocalRowFrame

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
variable {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
variable {group : Fin ar.header.d → Fin (R+1)} {F : TeamRows.Returns (Fin (R+1)) ar w}
variable {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
variable {template : Frame} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {count : ℕ}

open CellSparse.Packet.Source
open private host_order from OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostFits

open DiagonalTallyCellReports

/-- Retain the complete original site, including every mark, tally and padding bit, across
the actual routed and owned-group runs on this receiving team. -/
theorem SharedWriters.owned_bundle_at (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q)
    (u : Fin (R+1)) (l : ReportLayout) (bundle : ReportBundle) (description : ℕ)
    (begins : ar.cellBank ≤ bundle.header.siteSlot) (ends : bundle.header.siteSlot+description ≤ ar.stop)
    (arrived : bundle.delivered l description (readings (H u).history.val.2.2)) :
    bundle.delivered l description (readings (F.output u)) := by
  have low : ar.publicBase ≤ ar.cellBank := (Nat.le_add_right ..).trans (host_order ar).2.1
  intro bit
  have inRange := bit.isLt
  have stored := writer.owned_delivery_word symbols handoff receipt u (bundle.header.siteSlot+bit.val)
    (by omega) (Or.inl (by omega))
  exact (congrArg Fin.val stored).trans (arrived bit)

end TeamContraction

namespace FiniteEvaluator.CubeAllocation

open BorderVNP.Cube RoutingISA Packing Crossing
open CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs DiagonalTallyCellReports

/-- The host scatter writes only in the supplied prefix of each actual cable endpoint.
The complete original interval in its claimed cell therefore survives, including unused
padding and all tally-sidecar positions needed by the native signed report reader. -/
theorem hostImage_bundle_at (ar : CubeArena.Layout) (frame : ℕ) (returned : ℕ → ℕ)
    {D m s n d k b J P₀ origin : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin ar.cells) (aux : N.Site → ℕ)
    (sites : N.Site ↪ Fin s) (edges : N.Edge ↪ Fin m) (ports : P ↪ Fin n)
    (F : Fields s m n ar.cells d k b σ) {x : σ → Bool} {old : Fin J → Fin s} {live : Fin P₀ → Fin n}
    (rep : Represents N cell aux sites edges ports F x) (ids : ∀ c, (F.cells c).val=c.val)
    (room : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (space : ∀ c, suppliedSize N cell c ≤ ar.cellStride)
    {geo : ℕ → ℕ} (hdr : Header frame origin m ar.cells J returned) (img : Image F old live x origin geo)
    (sectionWords : ∀ z, origin ≤ z → z < origin+5*m → returned z=geo z)
    (pointer : returned (frame+72)=ar.hostDirectory)
    (banks : ∀ c<ar.cells, returned (ar.hostDirectory+2*c+1)=ar.cellBank+c*ar.cellStride)
    (c : Fin ar.cells) (l : ReportLayout) (bundle : ReportBundle) (description : ℕ)
    (above : ar.cellBank+c.val*ar.cellStride+suppliedSize N cell c ≤ bundle.header.siteSlot)
    (inside : bundle.header.siteSlot+description ≤ ar.cellBank+c.val*ar.cellStride+ar.cellStride)
    (entry : bundle.delivered l description returned) :
    bundle.delivered l description (OpenSuffix.hostImage frame returned) := by
  let base := ar.cellBank+c.val*ar.cellStride
  let offset := bundle.header.siteSlot-base
  have low : base+suppliedSize N cell c ≤ bundle.header.siteSlot := above
  have high : bundle.header.siteSlot+description ≤ base+ar.cellStride := inside
  have address : bundle.header.siteSlot=base+offset := by dsimp only [offset]; omega
  have ends := host_ends_supplied ar frame returned N cell aux sites edges ports F rep ids room hdr img sectionWords
  intro bit
  have bfit := bit.isLt
  have avoid := host_avoids_private ar frame returned (fun v => suppliedSize N cell v) space
    pointer banks ends c (offset+bit.val) (by omega) (by omega)
  have read := HostScatter.Layout.prefix_outside (HostScatter.Layout.fromFrame frame returned) returned
    (HostScatter.Layout.fromFrame frame returned).count (base+(offset+bit.val)) avoid
  change OpenSuffix.hostImage frame returned (bundle.header.siteSlot+bit.val)=_
  rw [address, Nat.add_assoc]
  exact read.trans (by simpa only [address,Nat.add_assoc] using entry bit)

end FiniteEvaluator.CubeAllocation


namespace TeamContraction

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator Packing Crossing FiniteEvaluator
open CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs DiagonalTallyCellReports

/-- The actual data-writer, published seven-word directory and control-entry return together
transport every bit of a received original site into its physical signed report source. -/
theorem FrozenControlEntry.published_bundle_at {t : SignedTaskArena.Layout} {prog : OpenSuffix.Inputs}
    {frame current control offsets w raw gap origin : ℕ} {dir : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {profile placed out : Memory w} {input written : ℕ → ℕ} {axis : Fin (t.cube.n+1)} {R : ℕ}
    (entry : NativeEntry t.cube frame control axis R input
      (readings (Directory.ISA.publish placed frame raw (dir.directory pp lp))) written)
    {D s n d k b P₀ : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin t.cube.cells) (aux : N.Site → ℕ)
    (sites : N.Site ↪ Fin s) (edges : N.Edge ↪ Fin t.cube.cables) (ports : P ↪ Fin n)
    (F : Fields s t.cube.cables n t.cube.cells d k b σ)
    {x : σ → Bool} {old : Fin dir.entries → Fin s} {live : Fin P₀ → Fin n}
    (controlEntry : FrozenControlEntry t prog frame current control offsets w (fun c => suppliedSize N cell c) written (readings out))
    (rep : Represents N cell aux sites edges ports F x) (ids : ∀ c, (F.cells c).val=c.val)
    (room : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (space : ∀ c, suppliedSize N cell c ≤ t.cube.cellStride)
    (hdr : Header frame origin t.cube.cables t.cube.cells dir.entries (readings profile))
    (image : Image F old live x origin (readings profile))
    (placement : (privateLayout frame origin t.cube.cables t.cube.cells dir.entries dir.description gap).Image
      (readings profile) dir.entries (readings placed))
    (first : frame+112 ≤ raw) (reserve : raw+7*dir.candidates ≤ origin)
    (geoEnd : origin+5*t.cube.cables ≤ t.cube.header.header)
    (l : ReportLayout) (bundle : ReportBundle) (c : Fin t.cube.cells)
    (above : t.cube.cellBank+c.val*t.cube.cellStride+suppliedSize N cell c ≤ bundle.header.siteSlot)
    (inside : bundle.header.siteSlot+dir.description ≤ t.cube.cellBank+c.val*t.cube.cellStride+t.cube.cellStride)
    (arrived : bundle.delivered l dir.description (readings out)) :
    bundle.delivered l dir.description (OpenSuffix.hostImage frame (readings out)) := by
  have kept : CubeAllocation.HostRetention t.cube frame
      (readings (Directory.ISA.publish placed frame raw (dir.directory pp lp))) written (readings out) :=
    ⟨controlEntry.retained.primary,
      fun z hi ne13 ne46 => (controlEntry.retained.lower z hi ne13 ne46).trans (entry.low z hi),
      controlEntry.retained.tables⟩
  have last := kept.header (published_routing_header pp lp placement hdr first reserve)
  apply CubeAllocation.hostImage_bundle_at t.cube frame (readings out) N cell aux sites edges ports F
    rep ids room space last image _ controlEntry.placement.pointer controlEntry.placement.bank c l bundle dir.description
    above inside arrived
  intro z lo hi
  exact (kept.geometry (by omega) z lo (hi.trans_le geoEnd)).trans
    (published_cable_words pp lp placement first reserve z lo hi)

end TeamContraction


namespace RoutingISA.Evaluator.SignedPrep

open DiagonalTallyCellReports DiagonalTallyCellReports.ReportDirectory

/-- Membership of an actual visited original bundle identifies its true receiving team,
also after changing report use flags, tally digits, or physical layout indices. -/
theorem SameReportCells.source_owner {l l' : ReportLayout} {C J : ℕ}
    {cs : List (ReportCell l)} {host : Fin J → Fin C} {payload : Fin J → ReportBundle}
    {team : ℕ} {who bank supply privateWidth : ℕ → ℕ} {digits : ℕ → Fin l'.gadgets → Fin l'.countWidth → Bool}
    (same : SameReportCells cs (sourceCells l' host payload team who bank supply privateWidth digits))
    (j : Fin J) (visited : ∃ c∈cs, (host j).val=c.number) : who (host j).val=team := by
  obtain ⟨c,inList,atCell⟩ := visited
  have member : (host j).val ∈ cs.map ReportCell.number :=
    List.mem_map.mpr ⟨c,inList,atCell.symm⟩
  rw [same.numbers] at member
  obtain ⟨row,arrived,num⟩ := List.mem_map.mp member
  obtain ⟨i,own,rfl⟩ := List.mem_map.mp arrived
  change i=(host j).val at num
  exact num ▸ of_decide_eq_true (List.mem_filter.mp own).2

end RoutingISA.Evaluator.SignedPrep

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator
open private detOfUnsigned from OAI.Computability.BorderVNP.CubeISALocalRowFrame

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
variable {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
variable {group : Fin ar.header.d → Fin (R+1)} {F : TeamRows.Returns (Fin (R+1)) ar w}
variable {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
variable {template : Frame} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {count : ℕ}

open DiagonalTallyCellReports DiagonalTallyCellReports.ReportDirectory RoutingISA.Evaluator.SignedPrep

/-- Each actually visited site uses the delivery to its own routed team. The membership
test is read from the computed signed report directory, and the protected memory word
comes from the return on that same team for every original descriptor bit. -/
theorem SharedWriters.owned_report_deliveries (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q)
    (u : Fin (R+1)) {l l' : ReportLayout} {J : ℕ} (description : ℕ) (host : Fin J → Fin ar.cells)
    (packets : Fin J → ReportBundle) {rows : List (ReportCell l)} {templatePackets : Fin J → ReportBundle}
    {who bank supply privateWidth : ℕ → ℕ} {digits : ℕ → Fin l'.gadgets → Fin l'.countWidth → Bool}
    (same : SameReportCells rows (sourceCells l' host templatePackets u.val who bank supply privateWidth digits))
    (ownerAt : ∀ c : Fin ar.cells, who c.val=(owner c.val).val)
    (begins : ∀ j, ar.cellBank ≤ (packets j).header.siteSlot)
    (ends : ∀ j, (packets j).header.siteSlot+description ≤ ar.stop)
    (delivered : ∀ j, (packets j).delivered l description (readings (H (owner (host j).val)).history.val.2.2)) :
    ∀ j, (∃ c∈rows, (host j).val=c.number) →
      (packets j).delivered l description (readings (F.output u)) := by
  intro j visited
  have atTeam : owner (host j).val=u := Fin.ext ((ownerAt _).symm.trans (same.source_owner j visited))
  have arrived := delivered j
  rw [atTeam] at arrived
  exact writer.owned_bundle_at symbols handoff receipt u l (packets j) description (begins j) (ends j) arrived

end TeamContraction

end BorderVNP
end Computability
end OAI
