import OAI.Computability.BorderVNP.DiagonalFrozenOwnedBundleTransport

/-! # Complete received original reports on the actual owned control entry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Crossing Packing CellAddresses DiagonalTallyCellReports RoutingISA

/-- All marked words in the routed receiving cell, their physical bank bounds, and the
room for interpreting the header, original factors and native tally sidecar. -/
structure OriginalReportDelivery {D C w teams : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (t : SignedTaskArena.Layout) (dir : Directory.Layout) (N : Network D P bits)
    (cell : N.Site → Fin C) (hosts : Fin dir.entries → N.Site) (owner : ℕ → Fin teams)
    (issued : Fin teams → Memory w) (report : ReportLayout) (packets : Fin dir.entries → ReportBundle) : Prop where
  cells : C=t.cube.cells
  words : ∀ j, (packets j).delivered report dir.description (readings (issued (owner (cell (hosts j)).val)))
  supplied : ∀ c, suppliedSize N cell c ≤ t.cube.cellStride
  lower : ∀ j, t.cube.cellBank+(cell (hosts j)).val*t.cube.cellStride+suppliedSize N cell (cell (hosts j)) ≤
    (packets j).header.siteSlot
  upper : ∀ j, (packets j).header.siteSlot+dir.description ≤
    t.cube.cellBank+(cell (hosts j)).val*t.cube.cellStride+t.cube.cellStride
  site : ∀ j, (packets j).SiteRoom report w dir.description

/-- Transport the public enumeration to the cube parameter's definitionally indexed cell
type. This preserves the exact numeric addresses and works with controls indexed by the
allocator even when equality of the two rounded cover counts uses a depth equation. -/
theorem OriginalReportDelivery.onCube {D C w teams : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {t : SignedTaskArena.Layout} {dir : Directory.Layout} {N : Network D P bits} {cell : N.Site → Fin C}
    {hosts : Fin dir.entries → N.Site} {owner : ℕ → Fin teams} {issued : Fin teams → Memory w}
    {report : ReportLayout} {packets : Fin dir.entries → ReportBundle}
    (original : OriginalReportDelivery t dir N cell hosts owner issued report packets) :
    OriginalReportDelivery t dir N (Fin.cast original.cells ∘ cell) hosts owner issued report packets := by
  have h := original.cells
  subst C
  exact original

open VPVNP Diagonal.Layout RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator CellAddressCircuit CellAddressPhysical RoutingOutputs
open DiagonalTallyCellReports.ReportDirectory RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open private detOfUnsigned from OAI.Computability.BorderVNP.CubeISALocalRowFrame

variable {R r time pins link inner n w : ℕ} {Edge : Type} {G : Wiring R r time pins link inner n Edge}
variable {pin : Fin pins → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {dir : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)}
variable {H : Fin (R+1) → TeamHistory w} {layout : Fin (R+1) → Pins.Layout}
variable {t : SignedTaskArena.Layout}
variable {issuedDir : Packing.Directory.Layout} {issuedPP issuedLP : ℕ → ℕ × ℕ} {start stride : ℕ}
variable {f : ReturnedDelivery G pin ext L issuedDir issuedPP issuedLP owner start stride H layout}
variable {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
variable {decl : LengthDeclaration t.cube.n t.cube.header.d}
variable {group : Fin t.cube.header.d → Fin (R+1)} {result : TeamRows.Returns (Fin (R+1)) t.cube w}
variable {owners : (Packet t.cube.n t.cube.header.d t.cube.header.blocks → Selector t.cube.n t.cube.K t.cube.h) →
  Fin t.cube.header.d → Fin (R+1)}
variable {template : Frame} {id : TableEntry t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s → ℕ} {count : ℕ}

/-- The marked-report premise of the actual returned report builder. A visited row's
receiving team is determined by the checked source directory, and the host scatter on
that execution changes only the supplied data before the indicated original report. -/
theorem OriginalReportDelivery.hostImage {D C : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} {cell : N.Site → Fin C} {hosts : Fin dir.entries → N.Site}
    {report : ReportLayout} {packets : Fin dir.entries → ReportBundle}
    (original : OriginalReportDelivery t dir N cell hosts owner (fun u => (H u).history.val.2.2) report packets)
    (u : Fin (R+1)) (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) t.cube.header.blocks t.cube.K t.cube.h decl group)
    (handoff : OwnedHandoff f g src t.cube decl group template id count result)
    {q : NativeAssignments.Routed (b:=t.cube.b) (s:=t.cube.s) owners}
    (observed : ObservedOwned t.cube decl group result owners (f.receivedRows g group) q)
    {l' : ReportLayout} {rows : List (ReportCell report)} {source : Fin dir.entries → ReportBundle}
    {who bank supply privateWidth : ℕ → ℕ} {digits : ℕ → Fin l'.gadgets → Fin l'.countWidth → Bool}
    (same : SameReportCells rows (sourceCells l' (cell ∘ hosts) source u.val who bank supply privateWidth digits))
    (ownerAt : ∀ c : Fin C, who c.val=(owner c.val).val)
    {prog : OpenSuffix.Inputs} {frame current control offsets raw gap origin : ℕ}
    {axis : Fin (t.cube.n+1)} {input written : ℕ → ℕ} {profile placed : Memory w}
    (entry : NativeEntry t.cube frame control axis R input
      (readings (Directory.ISA.publish placed frame raw (dir.directory pp lp))) written)
    {sz np levels keyWidth field portsN : ℕ} {σ : Type} [Fintype σ]
    (aux : N.Site → ℕ) (sites : N.Site ↪ Fin sz) (edges : N.Edge ↪ Fin t.cube.cables) (ports : P ↪ Fin np)
    (F : Fields sz t.cube.cables np C levels keyWidth field σ) {x : σ → Bool} {live : Fin portsN → Fin np}
    (controlEntry : FrozenControlEntry t prog frame current control offsets w
      (fun c => suppliedSize N cell (Fin.cast original.cells.symm c)) written (readings (result.output u)))
    (rep : Represents N cell aux sites edges ports F x) (ids : ∀ c,(F.cells c).val=c.val)
    (room : ∀ c,guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^field)
    (hdr : Header frame origin t.cube.cables C dir.entries (readings profile))
    (image : Image F (sites ∘ hosts) live x origin (readings profile))
    (placement : (privateLayout frame origin t.cube.cables C dir.entries dir.description gap).Image
      (readings profile) dir.entries (readings placed))
    (first : frame+112≤raw) (reserve : raw+7*dir.candidates≤origin) (geoEnd : origin+5*t.cube.cables≤t.cube.header.header) :
    ∀ j, (∃ c ∈ rows, (cell (hosts j)).val=c.number) →
      (packets j).delivered report dir.description (OpenSuffix.hostImage frame (readings (result.output u))) ∧
      (packets j).SiteRoom report w dir.description := by
  have equality := original.cells
  subst C
  have begins j : t.cube.cellBank ≤ (packets j).header.siteSlot := by have bound := original.lower j; omega
  have ends j : (packets j).header.siteSlot+dir.description ≤ t.cube.stop := by
    have bound := original.upper j
    have top := Nat.mul_le_mul_right t.cube.cellStride (cell (hosts j)).isLt
    rw [Nat.succ_mul] at top
    change _ ≤ t.cube.cellBank+t.cube.cells*t.cube.cellStride
    omega
  have held := writer.owned_report_deliveries symbols handoff observed u dir.description (cell ∘ hosts) packets
    same ownerAt begins ends original.words
  intro j visited
  refine ⟨?_,original.site j⟩
  exact controlEntry.published_bundle_at entry N cell aux sites edges ports F rep ids room original.supplied hdr image
    placement first reserve geoEnd report (packets j) (cell (hosts j)) (original.lower j) (original.upper j) (held j visited)

end TeamContraction

end BorderVNP
end Computability
end OAI
