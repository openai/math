import OAI.Computability.BorderVNP.DiagonalSignedOwnedOpaque
import OAI.Computability.BorderVNP.DiagonalSignedPointerReportRead

/-! # The original signed descriptor on the actual owned and report returns -/

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

/-- Transfer a complete original verifier body from the actual routed
receiver to the returned team's owned-group memory at the emitted address. -/
theorem SharedWriters.owned_body_at (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q)
    (u : Fin (R+1)) (addr head description : ℕ) (fs : List CellSparse.Factor)
    (begins : ar.cellBank≤addr) (ends : addr+description≤ar.stop)
    (arrived : Delivered (description:=description) (readings (H u).history.val.2.2) addr head fs) :
    Delivered (description:=description) (readings (F.output u)) addr head fs := by
  intro b used
  have above : ar.publicBase≤ar.cellBank := (Nat.le_add_right ..).trans (host_order ar).2.1
  have byte := b.isLt
  have kept := writer.owned_delivery_word symbols handoff receipt u (addr+b.val) (by omega) (Or.inl (by omega))
  exact (congrArg Fin.val kept).trans (arrived b used)

end TeamContraction

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM RoutingISA.Evaluator FiniteEvaluator Packing Crossing
open CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs BorderVNP.Cube
open CellSparse.Packet.Source (Delivered)
open private host_order from OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostFits

variable (a : Layout) {team frame offsets control live portCount bundles b bits : ℕ}
    (owner : Fin bundles → Fin a.cube.cells) (header : Fin bundles → BottomReports.BundleHeader)
    {D s m n d k J A origin : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {width : P → ℕ}
    (N : Network D P width) (cell : N.Site → Fin a.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : Fields s m n a.cube.cells d k bits σ) {x : σ → Bool} {original : Fin J → Fin s} {ports : Fin A → Fin n}
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^bits)
    (space : ∀ c, suppliedSize N cell c ≤ a.cube.cellStride)
local notation "H" => a.openInputs team frame offsets control live portCount bundles b owner header

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {entry : Memory w}
    {geo : ℕ → ℕ} (atFrame : (pub 0).val=frame)
    (oldFrame : Header frame origin m a.cube.cells J (readings entry)) (image : Image F original ports x origin geo)
    (retained : ∀ z, origin ≤ z → z<origin+5*m → readings entry z=geo z)
    (first : frame+112 ≤ a.cube.header.header)
    (ready : OpenSuffix.Ready (a.openInputs team frame offsets control live portCount bundles b owner header)
      frame (readings entry) w)
    (placed : OpenSuffix.Placement (a.openInputs team frame offsets control live portCount bundles b owner header)
      a.cube a.before frame (readings entry))
    (opened : Returns OpenSuffix.code pub mac reg entry)

open DiagonalTallyCellReports

include rep codes fit space oldFrame image retained atFrame first ready placed in
/-- A true receiving address above this cell's supplied prefix and every
emitted report choice survives the opened host controls and signed report.
Both endpoints are actual native returns, with the same original ordinal. -/
theorem Layout.reported_body_at {axis : Fin (a.cube.n+1)} {reportDescription packet : ℕ}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    (allocation : ReportAllocation a.before a.after (a.cube.cellWriter frame control axis) l cs q)
    (seed : PreparedReportInput pub opened.val.2.2 cs q reportDescription)
    (report : Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    (c : Fin a.cube.cells) (slot head : ℕ) (fs : List CellSparse.Factor)
    (low : a.cube.cellBank+c.val*a.cube.cellStride+suppliedSize N cell c≤ slot)
    (high : slot+packet≤a.cube.cellBank+c.val*a.cube.cellStride+a.cube.cellStride)
    (tails : ∀ row∈cs, row.number=c.val → a.cube.cellBank+c.val*a.cube.cellStride+row.supplied+row.tailWidth≤ slot)
    (received : Delivered (description:=packet) (readings entry) slot head fs) :
    Delivered (description:=packet) (readings report.val.2.2) slot head fs := by
  let bank := a.cube.cellBank+c.val*a.cube.cellStride
  let start := slot-bank
  have addr : bank+start=slot := by dsimp only [bank,start]; omega
  have old : Delivered (description:=packet) (readings entry) (bank+start) head fs := addr ▸ received
  have rowBound (row : ReportCell l) (member : row∈cs) (same : row.number=c.val) : row.supplied+row.tailWidth≤ start := by
    have enough := tails row member same
    dsimp only [start,bank]
    omega
  have save := a.reported_delivered owner header N cell aux siteID edgeID portID F rep codes fit space
    atFrame oldFrame image retained first ready placed opened allocation seed report c start head fs
    (by dsimp only [start,bank]; omega) (by dsimp only [start,bank]; omega) rowBound old
  change Delivered (description:=packet) (readings report.val.2.2) (bank+start) head fs at save
  rwa [addr] at save

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
