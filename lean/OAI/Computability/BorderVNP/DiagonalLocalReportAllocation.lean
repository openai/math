import OAI.Computability.BorderVNP.DiagonalSignedReportEntry
import OAI.Computability.BorderVNP.DiagonalSignedFrozenReportRows
import OAI.Computability.BorderVNP.DiagonalCanonicalReportDirectory
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomReportRows
import OAI.Computability.BorderVNP.DiagonalFrozenReportSupplyStride

/-! # Allocating a returning team's own original report directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes BottomReports Cover TeamContraction GridPlacement
open Diagonal.CellEntries Diagonal.ExternalSew DiagonalTallyCellReports DiagonalTallyAllocation RoutingISA
open SignedTaskArena FiniteEvaluator ReportDirectory Packing.BundleDirectory
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical BigOperators

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {N leaves copies : ℕ} (origin : Fin N ≃ Fin leaves × (Fin q → Deck (depth+2)))
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin s) (edges : (W.routedFine position).Edge ↪ Fin m)
    (ports : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa)
    (slot base : Fin N → ℕ) (bank : Fin N → ℕ → Bool)
    (task : SignedTaskArena.Layout) (home : Fin N → Fin task.cube.cells)
    (teamNumbers : Fin leaves × Fin copies ↪ Fin task.cube.teams)
    (params : GrammarLabel (Fin n × Bool) (Fin g) n ↪ Fin task.p.parameters)
    {frame ctl team offsets live nports b w : ℕ}

local notation3 (prettyPrint := false) "src" => W.retainedBundle (copies:=copies) position origin code sites edges ports channels groups slot base bank
local notation3 (prettyPrint := false) "prog" => task.openInputs team frame offsets ctl live nports N b home (ReportBundle.header ∘ src)
local notation3 (prettyPrint := false) "dir" => task.bundleLayout frame ctl N
local notation3 (prettyPrint := false) "ctrl" => task.controlRows team frame offsets ctl live nports
local notation3 (prettyPrint := false) "rep" => reportLayout task.before task.after frame ctl task.p.parameters task.p.siteWidth task.p.bodyCap task.cube.stop
local notation3 (prettyPrint := false) "reserve" => reportBounds task.cube (leaves*GridHosts.tileCount q depth)
  (seedSiteCapacity n r q depth) task.p.parameters (Nat.clog 2 (r*(2*d.val+1)+1)) task.p.report.gadgets w

include teamNumbers params in
/-- The scanner's original cell list is allocated on the memory of this team's
own opening. Each stable source row comes from its real wired seed. -/
theorem localDirectory_allocation (axis : Fin (task.cube.n+1)) (owned : ℕ → ℕ)
    (digits : ℕ → Fin task.p.report.gadgets → Fin task.p.report.countWidth → Bool)
    (room : task.OpenRoom frame offsets ctl live nports N (2^b) w)
    (place : OpenSuffix.Placement prog task.cube task.before frame owned)
    (layout : task.p.report=reserve)
    {wp wd X P L reader : ℕ}
    (windows : task.FinishWindows r w wp wd (Nat.clog 2 (r*(2*d.val+1)+1)) X P L reader)
    (rpos : 1≤r) (stride : 3*(r*n)^2+1 ≤ task.cube.cellStride)
    (supplied : ∀ c : Fin task.cube.cells, owned (offsets+2*task.cube.cables+c.val) ≤ TeamScales.width n (1/5)) :
    let initial := grouped dir home src (OpenSuffix.hostImage frame owned)
    let original := directoryCells dir ctrl rep home src initial digits
    ReportAllocation task.before task.after (task.cube.cellWriter frame ctl axis) rep original task.after.reportCursor := by
  have ranges := physicalReportRows_room (copies:=copies) (fun _ : Fin leaves => W) position origin code
    (fun _ => sites) (fun _ => edges) ports channels groups slot base bank task.cube teamNumbers params
    task.p.report.gadgets w home
  have expanded : (∑ j,(src j).useCount) ≤ task.p.report.uses := by
    rw [layout]
    exact ranges.2.2.1
  have word : task.p.report.countWidth=w := congrArg Bounds.countWidth layout
  have uses : task.p.report.uses=task.cube.teams*(task.p.parameters*Nat.clog 2 (r*(2*d.val+1)+1)) :=
    congrArg Bounds.uses layout
  have receive c := windows.reportSupplyStride rpos (Nat.zero_lt_of_lt d.isLt) word uses stride
    src home expanded owned offsets c (supplied c)
  apply task.signedDirectoryAllocation home src place room axis digits receive
  · rw [layout]
    exact ranges.2.2.2
  · rw [layout]
    exact ranges.2.1
  · rw [layout]
    exact ranges.2.2.1

end Packing.DeckGrid.WiredWitness

namespace RoutingISA.SignedTaskArena

open FiniteEvaluator DiagonalTallyCellReports ReportDirectory Evaluator Packing RoutingOutputs DiagonalTallyAllocation

variable (task : Layout) {frame origin ports bundles R b w : ℕ} (u : Fin (R+1))
    (axis : Fin (task.cube.n+1)) (home : Fin bundles → Fin task.cube.cells)
    (payload : Fin bundles → ReportBundle)
local notation "table" => bases origin task.cube.cables task.cube.cells bundles
local notation "ctl" => controlsBase origin task.cube.cables task.cube.cells bundles ports
local notation "rows" => task.controlRows u.val frame (Bases.ends table) ctl (Bases.livePairs table) ports
local notation "file" => task.bundleLayout frame ctl bundles
local notation "rep" => reportLayout task.before task.after frame ctl task.p.parameters task.p.siteWidth task.p.bodyCap task.cube.stop
local notation3 (prettyPrint := false) "prog" => task.openInputs u.val frame (Bases.ends table) ctl (Bases.livePairs table) ports
  bundles b home (ReportBundle.header ∘ payload)

/-- The raw directory allocated on the owned return is precisely the
source-cell list submitted to the sparse report scanner on this prefix.
Each cell reads its bank, supplied width and private width from its
actual retained publication. -/
theorem Layout.localDirectory_sourceCells (prof initial written owned : ℕ → ℕ)
    (entry : NativeEntry task.cube frame ctl axis R prof initial written)
    (keep : CubeAllocation.HostRetention task.cube frame initial written owned)
    (place : OpenSuffix.Placement prog task.cube task.before frame owned)
    (room : task.OpenRoom frame (Bases.ends table) ctl (Bases.livePairs table) ports bundles (2^b) w)
    (after : ℕ → ℕ)
    (assignment : ∀ c : Fin task.cube.cells, (rows).owner after c.val=(task.cube.receivingOwner frame axis R prof c.val).val)
    (digits : ℕ → Fin task.p.report.gadgets → Fin task.p.report.countWidth → Bool) :
    let middle := grouped file home payload (OpenSuffix.hostImage frame owned)
    directoryCells file rows rep home payload middle digits =
      sourceCells rep home payload u.val ((rows).owner after)
        (fun c => task.cube.cellBank+c*task.cube.cellStride)
        (fun c => initial ((table).ends+2*task.cube.cables+c))
        (fun c => initial ((table).livePairs+2*ports+c)) digits := by
  intro middle
  apply directoryCells_sourceCells rep file rows home payload middle rfl
  intro c hc
  have words := task.signedReportColumns u axis home payload prof initial written owned entry keep place room ⟨c,hc⟩
  exact ⟨words.1.trans (assignment ⟨c,hc⟩).symm,words.2⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
