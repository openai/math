import OAI.Hierarchy.TaggedWideCalendarEndpointFields
import OAI.Hierarchy.TaggedWideMaskWord
import OAI.Hierarchy.TaggedWideRankedChecks
import OAI.Hierarchy.TaggedWideFundedHistoryMask
import OAI.Hierarchy.TaggedWidePathFirstNetwork

namespace OAI
/-! # The history mask on the final output of the selected native program -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open ThreeFlat.Routing
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x) (room : cpu.SiteRoom)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unit
local notation "S" => v.wideInstalledSize x m ell unit g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unit g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unit g
    (v.wide_dated_sites h width ell unit) (v.wide_dated_edges h width ell unit) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "D" => v.parentShared x m ell short unit ((es).length+1)
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
local notation "base" => v.wideOrigin h width S seed
variable (Z : CalendarTerms F h d k width (fuel v.mesh*width) v.radius 1 sl es base)
local notation "rout" => Z.nativeRouting D
local notation "sites" => SignedSites.ofCalendar (cpu:=cpu) Z control v.calendarTerminalWidth
  (v.calendarTerminalPins x m ell short)
local notation "source" => fun _ : Fin (m+1)=>slots
local notation "count" => purchaseModules v.W u δ ξ menu x
local notation "target" => fun i=>purchaseCandidates h v.W k v.wideJobs slots ((menu).height i x) (count i)
local notation "Buy" => PurchaseList (F:=F) (C:=C) menu x source target count
local notation "Ex" => OpenPins h width (rout).catalyst
local notation "report" π:arg j:arg => v.wide_reported_path h width S π seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words j
variable (sourceRows : ∀(π:Equiv.Perm (Tagged.Row x.h)) (j:Path sl es (base π)),reportGeometry π (Z.reported π j)=reportGeometry π (report π j))
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
variable (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
local notation "path" => (Fintype.equivFin (Path sl es (base perm))).symm i
local notation "record" => CalendarTape.encode sl es (base perm) path
local notation "runAt" => v.wide_selected_local_return m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "finishAt" => (runAt).2.2.2
local notation "windowAt" => (finishAt).choose_spec.2.2.2.2
local notation "joinedRows" => (sourceRows perm path).trans
  (v.wide_selected_geometry m ell short u δ ξ unit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag path)


open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.BranchRoles Tagged.WideCalendarSites Tagged.WideStack.Leaf
local notation "tree" p:arg => Prefix.cursorSlot («slot»:=sl) (events:=es) (x₀:=base p)
local notation "fundedWidth" p:arg => Prefix.atWidth («slot»:=sl) (events:=es) (x₀:=base p) («S»:=siteLast h d k+1) (fun {_ _} c=>v.wideCursorWidth h width S p seed cpu.age cpu.ready.credit cpu.ready.size_le c)
variable (height : v.BranchRoleHeight h width)
    (widthSource : ∀p, Prefix.atWidth (Z.width p) = fundedWidth p)
local notation "root" => (Prefix.start : Prefix sl es (base perm) es (base perm))
local notation "top" => Prefix.atCursor root
local notation "branch" => Prefix.histories root path
local notation "public" => CoreBoard.HistoryRoles.Public v.sampler h v.W k v.wideJobs
local notation "roles" => HistoryRoles.ceiling v.sampler («h»:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unit v.keepLimit (fuel v.mesh) width
local notation "n" => ((es).length+1)*Fintype.card ((r:public)×Fin (roles r))
local notation "rows" => v.widePathCells h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)

local notation "placement" => v.wideCalendarPartyPlace m ell short u δ ξ x cpu Z perm i height widthSource
local notation "G" => (v.wideFullGates x m ell short u δ ξ unit cpu.room).2
local notation "history" => v.wideHistoryGate («Ex»:=Ex) (Se:=Fin (rout).selectors) x m ell short u δ ξ unit cpu.room room.history
local notation "geom" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "dir" => WideMemory.dir x.h v.W k v.wideJobs
local notation "ports" => WideMemory.H x.h v.W k v.wideJobs
local notation "view" => v.wideHistoryUnit unit*width
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unit g
local notation "ri" => CalendarTerms.RankedRows (F:=F) (geom).index D (dir).groups ports (2^ell) width m n view
local notation "lastOut" => (finishAt).choose
local notation "seen" => (G).terminal lastOut
local notation "reach" => timelineFin (tree perm) (fundedWidth perm) rows es top branch

-- Use the selected row receipt already present in this particular endpoint check.
attribute [local irreducible] CalendarTerms.RankedRows.Check

open Lean Elab Tactic Meta in
local elab "transportHistoryOnSelectedBranch " predicate:ident : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let checkExpr ← Meta.whnf (← goal.getType)
    unless checkExpr.isAppOf ``CalendarTerms.RankedRows.Check do
      throwError "expected the selected ranked-row check, got {checkExpr.getAppFn.constName?}"
    let operands := checkExpr.getAppArgs
    let row := operands[operands.size - 3]!
    unless row.isAppOf ``CalendarTerms.RankedRows.onBranch do
      throwError "expected the selected rank, got {row.getAppFn.constName?}"
    let pred ← Meta.getFVarFromUserName predicate.getId
    let rowArgs := row.getAppArgs
    let op := mkAppN (← Meta.mkConstWithFreshMVarLevels ``CalendarTerms.RankedRows.onBranch_property) (rowArgs.push pred)
    let premiseType ← Meta.whnf (← Meta.inferType op)
    unless premiseType.isForall do throwError "expected the row predicate's original-board premise"
    let premise ← Meta.mkFreshExprSyntheticOpaqueMVar premiseType.bindingDomain!
    goal.assign (mkApp op premise)
    replaceMainGoal [premise.mvarId!]

/-- The ranked-row transport changes the type of the edge assignment. The
chronological bits and the public output memory are independent of that type. -/
theorem wide_calendar_history_mask
    (word : WideParent.columnBits view≤(G).W) :
    v.wideCalendarEndpointField (C:=C) m ell short u δ ξ x cpu room control support Z sourceRows
      prices pricePos groupsFit metadata lanesFit buy e perm i tag height widthSource .historyMask := by
  intro kept
  let test (o:CalendarTerms.RowBoard) (r:ri o) : Prop :=
    ∀ a bits,TypedWiring.value history (CalendarTerms.readPins (B:=G) r.numbering e record seen
      (nativePins («view»:=view) (geom).index o.2 r.positive r.stage r.installed r.cap a bits))=
      if ∀j,bits j=true→j∈Set.range placement then 1 else 0
  transportHistoryOnSelectedBranch test
  intro flow bits
  refine Eq.trans ?_ (congrArg
    (fun cells:Set (Fin n) => if ∀j,bits j=true→j∈cells then (1:F) else 0)
    (v.wideCalendarPartyPlace_range m ell short u δ ξ x cpu Z perm i height widthSource).symm)
  have shelf : (g).rolesEnd S≤(g).workEnd S := by
    dsimp only [WideCPU.Dated.workEnd,WideCPU.Dated.slotStart,WideCPU.Dated.maskStart,
      WideCPU.Dated.controlStart,WideCPU.endOf]
    omega
  have after : (g).workEnd S+2≤(l).floor := v.wide_window_after_terminal x _
  apply v.widePath_history_mask (Se:=Fin (rout).selectors) x m ell short u δ ξ unit cpu.room height
    v.calendarUnit_rate perm seed path word _ _ _ (Equiv.refl _) _ e record _ lastOut flow bits
  · exact (runAt).2.2.1.2.2.2.1
  · intro addr haddr
    exact (finishAt).choose_spec.2.2.2.1 addr (by omega)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
