import OAI.Hierarchy.TaggedWideNumberedChordOrder
import OAI.Hierarchy.TaggedWidePathFinalAmounts
import OAI.Hierarchy.TaggedWideTerminalPlacement
import OAI.Hierarchy.TaggedWideTerminalParallelOrder
import OAI.Hierarchy.ProtocolRAMTurnReportEvidence

namespace OAI
/-! # Actual last-date role placement for the five-word funded terminal shelf -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets WireTelescope Tagged CalendarTape
open CoreBoard.PhysicalTerm Filter
open scoped Classical Fin.CommRing
set_option quotPrecheck false
-- The terminal proposition is addressed directly by its calendar consumers.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_path_terminal_packing"
set_option hygiene false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width size : ℕ)
    (π : Equiv.Perm (Tagged.Row h)) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
    (expanse : v.wideFundedSize h width v.maxBits ≤ size) (late : v.reportHeight ≤ h)
    (room : v.ReportWordRoom h width)
local notation "reader" => v.wideSelector h width age budget small
local notation "slots" => (reader).format.slot
local notation "es" => events v.mesh
local notation "start" => v.wideOrigin h width size seed π
local notation "table" => v.widePlacement h width
local notation "ceiling" => (v.privateArena table h width).endAddress v.mesh
local notation "stock" => v.fixedTerminalStock table h width
local notation "w" => Native.wordBits h (2^v.W) Native.copies
variable (j : Path slots es start)
local notation "raw" => (reader).format.windows.header es (encode slots es start j) seed
local notation "tape" => v.wideFundedRaw h width v.maxBits raw
local notation "checkout" => v.wideSignedCheckoutAt h width size stock v.radius π.symm
  (wideRouteOrder h (2^v.W) k) tape
local notation "pathReport" => v.wide_reported_path h width size π seed age budget small expanse late room j


open ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical
local notation "wire" => WireTelescope.CalendarTape.Prefix.atWidth («slot»:=slots) (events:=es) (x₀:=start) (S:=siteLast h (2^v.W) k+1) (fun {_ _} path => v.wideCursorWidth h width size π seed age budget small path)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans expanse
local notation "cap" c:arg => HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh c v.keepLimit (CatalystArchive.fuel v.mesh) width
variable (unitCost:ℕ)
    (replay:v.cursorReplayHeight≤h) (measure:v.wideDatedLedgerHeight≤h)
    (bounded : ∀(perm:Equiv.Perm (Fin (2^h))) (mem:Boot.Tape h (2^v.W)),
      let o:=wideRouteOrder h (2^v.W) k
      let m:=v.wideSignedMidAt h width size stock v.radius perm o mem
      let c:=v.wideSignedCheckoutAt h width size stock v.radius perm o mem
      c ceiling=0→v.DatedWireFits h width perm m c unitCost)



open Lean Elab Term in
local elab "compactPathNative " candidate:term : term => do
  let entry ← elabTerm candidate none
  unless entry.getAppFn.isConstOf ``wide_native_report do
    throwError "expected the original issued report"
  let result ← getConstInfo ``native_state_report_rows
  let some sourceCall :=  result.type.find? (fun e =>
    e.isApp && e.getAppFn.constName?.any (fun c => c.getString! == "terminalInputReport"))
    | throwError "the signed row projection contains no original report"
  let compact := mkAppN sourceCall.getAppFn entry.getAppArgs
  let typ ← Meta.whnf (← Meta.inferType compact)
  unless typ.getAppFn.isConstOf ``CoreBoard.Report do throwError "expected a fixed-board report"
  return compact

attribute [local irreducible] Nat.pow numberedBranchRoles
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit


local notation "catalog" => (table).catalogue
local notation "order" => v.wideOrder h width
local notation "pos" => v.wide_dated_bought_rows h width
local notation "q" => v.widePathRoles h width size π seed age budget small expanse late room j
  unitCost replay measure bounded
local notation "evidence" => v.wide_reported_path_funded_rows h width size π seed age budget small expanse late room j
local notation "admission" => Classical.choose evidence
local notation "bill" => Classical.choose (evidence).choose_spec
local notation "aliases" => fun {n : ℕ} (site : Fin n → Fin (Fintype.card (Columns h (2^v.W)) * k)) (fees : Fin n → ℕ) => (Classical.choose (evidence).choose_spec.choose_spec) site fees
local notation "Z" => compactPathNative (v.wide_native_report h width size π.symm raw v.maxBits expanse admission budget small
  bill (0:Word w) (aliases))
local notation "pad" => publicChord h (2^v.W) k
local notation "stop" => WireTelescope.CalendarTape.terminal WireTelescope.CalendarTape.Prefix.cursorSlot es (WireTelescope.CalendarTape.Prefix.atCursor WireTelescope.CalendarTape.Prefix.start) (WireTelescope.CalendarTape.Prefix.histories WireTelescope.CalendarTape.Prefix.start j)
local notation "atEnd" => v.widePathCells h width size π seed age budget small expanse late room j
  unitCost replay measure bounded stop
local notation "paid" => (Z).fixed
local notation "qty" => SettledMatrix.Layout.bits paid (Z).stock (Z).reserved (Z).used
local notation "full" => (Z).mount.actual.chordWidths paid+
  (commodityGraph π.symm (siteNumber h (2^v.W) k)).chordWidths (Z).stock+
  (catalystGraph (siteNumber h (2^v.W) k)).chordWidths (fun i=>(Z).reserved i-(Z).used i)
local notation "owner" => (catalog).original v.sampler π.symm v.depth (q).mark order
  (v.wideBoughtOrdinal h width π.symm (q).mark)
variable (A₀ : Alignment catalog v.sampler π.symm v.depth (q).mark v.radius (Z).rows
    (fun i=>((Z).rows i).width) owner)
local notation "id" => (Z).fixedOriginal v.depth (q).mark A₀.ident
local notation "namedRole" => Terminal.ports v.sampler π.symm v.depth (q).mark (q).exclusive paid
  (Z).stock (Z).reserved (Z).used id

private theorem selectedPackingChordOrder :
    let roleRows := v.widePathRoles h width size π seed age budget small expanse late room j
      unitCost replay measure bounded
    ∀ i j : Fin roleRows.count,
      HistoryRoles.sorted v.sampler π.symm v.depth roleRows.mark (roleRows.order i) =
        HistoryRoles.sorted v.sampler π.symm v.depth roleRows.mark (roleRows.order j) →
      (i < j ↔
        DatedRows.raw v.sampler π.symm v.depth roleRows.mark (table).catalogue
          (v.wideOrder h width) (v.wide_dated_bought_rows h width) roleRows.order i <
        DatedRows.raw v.sampler π.symm v.depth roleRows.mark (table).catalogue
          (v.wideOrder h width) (v.wide_dated_bought_rows h width) roleRows.order j) := by
  intro roleRows
  run_tac Lean.Elab.Tactic.withMainContext do
    let roles ← Lean.Meta.getLocalDeclFromUserName `roleRows
    let some value := roles.value? | throwError "expected the selected path roles"
    let numbered ← Lean.Meta.whnf value
    unless numbered.getAppFn.isConstOf ``numberedBranchRoles do
      throwError "expected the numbered roles of the actual funded path"
    let closure := Lean.mkAppN (Lean.mkConst ``numberedRoleChordOrder numbered.getAppFn.constLevels!) numbered.getAppArgs
    (← Lean.Elab.Tactic.getMainGoal).assign closure
    Lean.Elab.Tactic.replaceMainGoal []

/-- The last bits in the actual history are read by the terminal comparator in the original signed
matrix order, including independent labels whose paid chords coincide. -/
theorem wide_path_terminal_packing {F : Type} [Field F] {k : ℕ} {p «q» Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p «q» Q σ Λ) (h width size : ℕ)
    (π : Equiv.Perm (Tagged.Row h)) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
    (expanse : v.wideFundedSize h width v.maxBits ≤ size) (late : v.reportHeight ≤ h)
    (room : v.ReportWordRoom h width)
    (j : Path slots es start)
    (unitCost:ℕ)
    (replay:v.cursorReplayHeight≤h) (measure:v.wideDatedLedgerHeight≤h)
    (bounded : ∀(perm:Equiv.Perm (Fin (2^h))) (mem:Boot.Tape h (2^v.W)),
      let o:=wideRouteOrder h (2^v.W) k
      let m:=v.wideSignedMidAt h width size stock v.radius perm o mem
      let c:=v.wideSignedCheckoutAt h width size stock v.radius perm o mem
      c ceiling=0→v.DatedWireFits h width perm m c unitCost)
    (A₀ : Alignment catalog v.sampler π.symm v.depth (q).mark v.radius (Z).rows
    (fun i=>((Z).rows i).width) owner) :
    ∃ (head:full=wire stop) (fits:∀r:NamedAperture.LiveEnd qty,qty r.val.1≤(cap unitCost) (namedRole r)),
      atEnd=(NamedAperture.transport head.symm).toEmbedding.trans
        (Terminal.place v.sampler π.symm v.depth (q).mark (q).exclusive (Z).mount pad paid (Z).stock
          (Z).reserved (Z).used id (Z).receipt (cap unitCost) fits) := by
  let place (e : {e : Fin (Z).edges // 0<paid e}) :
      {e : Fin (Z).edges // 0<((Z).rows e).width} := ⟨e.val,(Z).fixed_live_width e.val e.property⟩
  have index (e : {e : Fin (Z).edges // 0<paid e}) :
      (catalog).ordinal v.sampler π.symm v.depth (q).mark order pos (id e)=e.val :=
    (v.wide_dated_original_ordinal h width π.symm (q).mark _).symm.trans (A₀.original (place e))
  have position (e : {e : Fin (Z).edges // 0<paid e}) :
      filledChord (Z).mount.actual pad e.val=sorted v.sampler π.symm v.depth (q).mark (.inl (id e)) :=
    Terminal.positions_of_reported v.sampler π.symm v.depth (q).mark (Z).mount pad paid (Z).stock
      (Z).reserved (Z).used id (Z).receipt (fun u=>A₀.joins (place u)) e
  let allRoles:=fun (l : WireTelescope.CalendarTape.Path slots es start)=>v.widePathRoles h width size π seed age budget small expanse late room l
    unitCost replay measure bounded
  apply BranchRoles.terminal_mapping
    (fun (c : WireTelescope.CalendarTape.Prefix.Cursor slots es start) =>v.wide_funded_continuation h width size arenaRoom π seed age budget small c.path)
    allRoles j (Z).mount pad (Z).receipt order pos id index position
  · exact v.wide_path_final_amounts h width size π seed age budget small expanse late room j
      unitCost replay measure bounded
  · exact v.selectedPackingChordOrder h width size π seed age budget small expanse late room j
      unitCost replay measure bounded

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
