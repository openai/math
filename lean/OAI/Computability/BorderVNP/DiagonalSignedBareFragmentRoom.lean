import OAI.Computability.BorderVNP.DiagonalSignedFragmentPublication

/-! # The fragment input before a signed argument return exists -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock Routing
open BorderVNP.Cube FiniteEvaluator CellMacro.Generator DiagonalTallyAllocation DiagonalTallyCellReports
open Packing Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs GeometryAdvice
open DiagonalTallyPacketEmit

variable {R w n s np bits lenBits cellBits dim : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {sizes : P → ℕ}
    (a : SignedTaskArena.Layout)
    (pub : Arg → Word w) {mac : TeamOpcode.Macros w 8} {bank : Bank w} {before : Memory w} (u : Fin (R+1))
    (opened : Returns Evaluator.SignedPrep.controls pub mac bank before)
    (reported : Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    (N : Network dim P sizes) (cell : N.Site → Fin a.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin a.cube.cables) (portID : P ↪ Fin np)
    (F : Fields s a.cube.cables np a.cube.cells cellBits lenBits bits σ) {x : σ → Bool}
    (dir : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (start prof gates words width tail : ℕ)
local notation3 (prettyPrint := false) "head" => readings pub 0
local notation3 (prettyPrint := false) "rows" => dir.directory pp lp
local notation3 (prettyPrint := false) "first" => start+7*dir.candidates
local notation3 (prettyPrint := false) "origin" => Allocation.dest (start+7*dir.candidates) prof gates words width
local notation3 (prettyPrint := false) "tables" => bases origin a.cube.cables a.cube.cells dir.entries
local notation3 (prettyPrint := false) "ctl" => controlsBase origin a.cube.cables a.cube.cells dir.entries (dir.teams*dir.sites)
local notation3 (prettyPrint := false) "out" => readings reported.val.2.2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Starting with the published geometry and the actual opened control
directory, every returned signed report fits the fragment RAM. The number
of raw deliveries is exactly the length of the compacted public directory. -/
theorem Layout.signed_fragment_room {geom placed : Memory w} {written input : ℕ → ℕ} {gap : ℕ}
    {original : Fin dir.entries → N.Site} {live : Fin (dir.teams*dir.sites) → P}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {banks : CellBanks.Layout}
    {description bankBits : ℕ} (owner : Fin dir.entries → Fin a.cube.cells)
    (hdr : Fin dir.entries → BottomReports.BundleHeader)
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val=c.val)
    (fieldFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^bits)
    (stride : ∀ c, suppliedSize N cell c ≤ a.cube.cellStride)
    (image : Image F (siteID ∘ original) (portID ∘ live) x origin (readings geom))
    (place : (privateLayout head origin a.cube.cables a.cube.cells dir.entries dir.description gap).Image
      (readings geom) dir.entries (readings placed))
    {readerIn readerGuess readerGates : ℕ} (high : a.endAddress w readerIn readerGuess readerGates < 2^w)
    (reserve : a.cube.header.header=Allocation.stop first prof gates words width w)
    (complete : a.cube.cables*3+(RoutingOutputs.count a.cube.cables a.cube.cells dir.entries (dir.teams*dir.sites)+
      ((a.cube.cells+(dir.entries+a.cube.cells))+(37+tail))) ≤ words)
    (base : head+112 ≤ start) (rawAt : readings placed (head+8)=start)
    (capacity : (rows).length+a.cube.header.d.choose 2 ≤ a.cube.maxRows)
    (wordsAt : ∀ i : Fin 37, written (ctl+i.val)=a.controls i.val)
    (axis : Fin (a.cube.n+1)) :
    let initial := readings (Directory.ISA.publish placed head start rows)
    let opens := a.openInputs u.val head (tables).ends ctl (tables).livePairs (dir.teams*dir.sites) dir.entries bankBits owner hdr
    Header head origin a.cube.cables a.cube.cells dir.entries initial →
    initial (head+92)=ctl → initial (head+72)=a.cube.hostDirectory →
    LabelIndex.Endpoints (LabelIndex.layout head initial) initial →
    NativeEntry a.cube head ctl axis R input initial written →
    CubeAllocation.HostRetention a.cube head initial written (readings before) →
    OpenSuffix.Ready opens head (readings before) w →
    OpenSuffix.Placement opens a.cube a.before head (readings before) →
    PreparedReportInput pub opened.val.2.2 cs q description →
    ReportAllocation a.before a.after banks l cs q → banks.bankStart=a.cube.cellBank →
    ∃ fr : FragmentDirectoryInput pub reported.val.2.2,
      (FragmentRows.Layout.fromFrame head out).Fits w out ∧ fr.layout.count=(rows).length ∧
      fr.bucket=a.fragments.bucket (fr.layout.stream out).length ∧ a.fragments.cells=fr.layout.cells ∧
      fr.layout.host.count=a.cube.cables ∧ fr.control=ctl ∧ (∀ i : Fin 37, out (ctl+i.val)=a.controls i.val) ∧
      FragmentRows.SparseGeometry a fr.layout (tables).ends ctl := by
  intro initial opens header control host endpoints entry keep ready position seed alloc bank
  have retained := a.signed_report_words owner hdr opened reported seed keep ready position alloc bank
  obtain ⟨fr,bucket,cells,cables,_,pointer,controls,geometry⟩ := retained.fragment_input
    pub reported.val.2.2 a N cell aux siteID edgeID portID F dir pp lp start prof gates words width tail
    rep codes fieldFit stride image place high reserve complete base rawAt capacity wordsAt axis header control host endpoints entry
  have limit := (FragmentRows.fragment_limit_le a w readerIn readerGuess readerGates).trans_lt high
  have last := (FragmentRows.arena_order a).2.2.2
  exact ⟨fr,fr.loaded ▸ fr.fit,(show fr.layout.count=(rows).length by rw [fr.loaded]; exact retained.compacted_count (by omega)),bucket,cells,cables,pointer,controls,geometry⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
