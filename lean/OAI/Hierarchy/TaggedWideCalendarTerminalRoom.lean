import OAI.Hierarchy.TaggedWideCalendarTerminalPins
import OAI.Hierarchy.TaggedWidePathTerminalPacking
import OAI.Hierarchy.TaggedWideBranchRoleHeight
import OAI.Hierarchy.TaggedWideFundedPrivateCells

namespace OAI
/-! # Physical word and aperture bounds at the actual final shelf -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets WireTelescope Tagged
open ThreeFlat.RAM PhysicalProcedure
open CoreBoard.PhysicalTerm CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph CalendarTape Filter
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
-- These indexed report fields are consumed through their original projections.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CalendarTerminalRoom"
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A)
-- Apply transitivity to the indexed width of the original admitted report.
theorem NativeReportRowsAtMost.mono {κ B : ℝ} {x : WideParent κ B} {lo hi : ℕ}
    (H : v.NativeReportRowsAtMost x lo) (h : lo ≤ hi) : v.NativeReportRowsAtMost x hi := by
  intro size extent π tape late stockRoom bounded cost state names placement stock checkout report accepted i
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let localTerm (n : Lean.Name) : Lean.Elab.Tactic.TacticM Lean.Expr := do
        return ← Lean.Meta.getFVarFromUserName n
      let evidence ← localTerm `H
      let arguments ← #[`size, `extent, `π, `tape, `late, `stockRoom, `bounded, `cost, `state, `names, `accepted, `i].mapM localTerm
      let smaller := Lean.mkAppN evidence arguments
      let target ← goal.getType
      let printed := target.getAppArgs[target.getAppNumArgs-2]!
      let lower ← localTerm `lo
      let upper ← localTerm `hi
      let increase ← localTerm `h
      goal.assign (Lean.mkAppN (Lean.mkConst ``Nat.le_trans) #[printed, lower, upper, smaller, increase])
    Lean.Elab.Tactic.replaceMainGoal []

local notation "h" => x.h
local notation "width" => x.w
local notation "unit" => v.calendarUnit
local notation "roomWidth" => v.calendarTerminalWidth
local notation "d" => 2^v.W
local notation "W" => Native.wordBits h d Native.copies
local notation "P" => v.widePlacement h width
local notation "stock" => v.fixedTerminalStock P h width
local notation "wall" => (v.privateArena P h width).endAddress v.mesh
local notation "o" => wideRouteOrder h d k

/-- Uniform across all dates and choices of the native report. The width of
each quotient row is measured on the original admitted checkout. -/
structure CalendarTerminalRoom : Prop where
  roles : TurnShelf.exponent v.wideShelfRoles≤ W
  digits : 2^TurnShelf.exponent (roomWidth*width)<2^W
  capacity : v.wideHistoryUnit unit*width≤ 2^TurnShelf.exponent (roomWidth*width)
  view : v.NativeReportRowsAtMost x (v.wideHistoryUnit unit*width)

theorem cofinal_calendar_terminal_room : ∀ᶠ x : WideParent κ A in WideParent.large κ A,v.CalendarTerminalRoom x := by
  have high : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  refine ((high.eventually (eventually_ge_atTop (TurnShelf.exponent v.wideShelfRoles))).and
    ((WideParent.fixed_mul_width (κ:=κ) (A:=A) (2*v.calendarTerminalWidth)).and
      (v.cofinal_private_report_rows (κ:=κ) (B:=A) v.sharpPaidUnit le_rfl))).mono ?_
  rintro x ⟨label, addr, allRows⟩
  have word : x.h≤ Native.wordBits x.h (2^v.W) Native.copies:=by
    rw [Native.wordBits_linear]
    exact (Nat.le_mul_of_pos_left _ (by decide : 0 < (2 : ℕ))).trans (Nat.le_add_right _ _)
  have pay:=TurnShelf.dyadic_room (v.calendarTerminalWidth*x.w)
    (Nat.mul_pos v.calendarTerminalWidth_pos x.formats.2.1)
  have endRoom : 2*(v.calendarTerminalWidth*x.w)<2^x.h:= by
    apply Nat.lt_of_succ_le
    simpa only [Nat.succ_eq_add_one, Nat.mul_assoc] using addr
  have raised : v.wideHistoryUnit v.calendarUnit*x.w≤ v.calendarTerminalWidth*x.w:=
    Nat.mul_le_mul_right _ (Nat.le_succ _)
  refine ⟨label.trans word,(pay.2.trans_lt endRoom).trans_le (Nat.pow_le_pow_right (by decide) word),
    raised.trans pay.1.le,?_⟩
  exact NativeReportRowsAtMost.mono v allRows (Nat.mul_le_mul_right x.w v.calendarUnit_view)

variable {v x}
variable (size : ℕ) (π : Equiv.Perm (Tagged.Row h)) (seed : Boot.Tape h d)
    (height : v.BranchRoleHeight h width) (extent : v.wideFundedSize h width v.maxBits≤ size)
local notation "reader" => v.wideSelector h width height.age height.credit height.small
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "orig" => v.wideOrigin h width size seed π
variable (j : Path sl es orig)
local notation "raw" => (reader).format.windows.header es (encode sl es orig j) seed
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

attribute [local irreducible] Nat.pow
  ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit


local notation "found" => v.wide_reported_path_funded_rows h width size π seed height.age height.credit
    height.small extent height.report height.wordRoom j
local notation "admitted" => Classical.choose found
local notation "bill" => Classical.choose (found).choose_spec
local notation "names" => fun {entries : ℕ} (site : Fin entries → Fin (Fintype.card (Columns h d)*k)) (fees : Fin entries → ℕ) => (Classical.choose (found).choose_spec.choose_spec) site fees
local notation "Z" => compactPathNative (v.wide_native_report h width size π.symm raw v.maxBits extent admitted height.credit
    height.small bill (0:Word W) (names))
local notation "bounds" => height.funded_aperture size unit extent v.calendarUnit_rate
local notation "q" => v.widePathRoles h width size π seed height.age height.credit height.small extent
    height.report height.wordRoom j unit height.replay height.measure bounds
local notation "order" => v.wideOrder h width
local notation "owner" => (P).catalogue.original v.sampler π.symm v.depth (q).mark order
  (v.wideBoughtOrdinal h width π.symm (q).mark)
local notation "qty" => SettledMatrix.Layout.bits (Z).fixed (Z).stock (Z).reserved (Z).used

/- Specialize the uniform row bound at the calendar's elected report and
its actual checkout. This selects the same dependent payment and naming witnesses
that occur in the statement of the funded-path theorem. -/
open Lean Elab Term in
local elab "fundedPathWidth " kind:ident boundTerm:term:arg witness:term:arg "["
    sz:term "," ext:term "," perm:term "," tape:term "," stockHeight:term "," smallHeight:term "," state:term "]" : term => do
  let boundProof ← elabTerm boundTerm none
  let checkedPath ← elabTerm witness none
  let baseArgs ← #[sz, ext, perm, tape, stockHeight, smallHeight, state].mapM fun term => do
    instantiateMVars (← elabTerm term none)
  let mut data := #[]
  let mut remainder := checkedPath
  let mut remainderType ← Meta.inferType checkedPath
  for _ in [:3] do
    let prop ← Meta.whnf remainderType
    unless prop.getAppFn.isConstOf ``Exists do throwError "expected a funded path witness"
    let #[carrier, child] := prop.getAppArgs | throwError "expected an indexed funded witness"
    let levels := prop.getAppFn.constLevels!
    let value := mkAppN (mkConst ``Classical.choose levels) #[carrier, child, remainder]
    remainder := mkAppN (mkConst ``Classical.choose_spec levels) #[carrier, child, remainder]
    remainderType := child.beta #[value]
    data := data.push value
  let conj ← Meta.whnf remainderType
  unless conj.getAppFn.isConstOf ``And do throwError "expected the signed checkout and rows"
  let accepted := mkAppN (mkConst ``And.left) (conj.getAppArgs.push remainder)
  let paidWidth := mkAppN boundProof #[baseArgs[0]!,baseArgs[1]!,baseArgs[2]!,baseArgs[3]!,data[0]!,baseArgs[4]!,baseArgs[5]!,data[1]!,baseArgs[6]!,data[2]!,accepted]
  if kind.getId == `statement then
    let widthAtIndex ← Meta.whnf (← Meta.inferType paidWidth)
    unless widthAtIndex.isForall do throwError "expected a bound on every returned row width"
    return widthAtIndex
  return paidWidth

/-- All returned widths of this same elected, completed path fit its
original public output operand. -/
theorem CalendarTerminalRoom.selectedView (H : v.CalendarTerminalRoom x) :
    fundedPathWidth statement (H.view) (found) [size, extent, π.symm, raw, height.credit, height.small, (0 : Word W)] :=
  fundedPathWidth proof (H.view) (found) [size, extent, π.symm, raw, height.credit, height.small, (0 : Word W)]


/-- The packed physical width of every original matrix coordinate fits the
same real dyadic shelf, through its named paid chronological role. -/
theorem CalendarTerminalRoom.settledBits (H : v.CalendarTerminalRoom x)
    (align : Alignment (P).catalogue v.sampler π.symm v.depth (q).mark v.radius (Z).rows
      (fun i=>((Z).rows i).width) owner) :
    ∀i,qty i≤ 2^TurnShelf.exponent (v.calendarTerminalWidth*width) := by
  let emission := v.wide_path_terminal_packing h width size π seed height.age height.credit height.small
    extent height.report height.wordRoom j unit height.replay height.measure bounds align
  let fit := Classical.choose (Classical.choose_spec emission)
  have caps:=HistoryRoles.ceiling_le («h»:=h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs)
    v.sampler v.mesh unit v.keepLimit (fuel v.mesh) width
  intro i
  by_cases pos : 0<qty i
  · let live : NamedAperture.LiveEnd qty:=⟨(i,false),pos⟩
    exact (fit live).trans ((caps _).trans H.capacity)
  · exact (Nat.eq_zero_of_not_pos pos).le.trans (Nat.zero_le _)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
