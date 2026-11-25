import OAI.Hierarchy.TaggedWideFundedReceiptCuts
import OAI.Hierarchy.TaggedWideParentSiteFrame

namespace OAI
/-! # The private widths and decoded plane of the paid calendar frame -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical BigOperators Fin.CommRing
open Tagged Tagged.WideStack
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
variable (unitCost : ℕ)

section
attribute [local irreducible] wide_native_report Native.wordBits CatalystArchive.recordCount
  CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit

/-- Every named terminal row of each admitted native report at this parent has bounded width. -/
abbrev NativeReportRowsAtMost {κ B : ℝ} (x : WideParent κ B) (bound : ℕ) : Prop :=
  ∀ (size : ℕ) (extent : v.wideFundedSize x.h x.w v.maxBits≤ size)
        (π : Equiv.Perm (Fin (2^x.h))) (raw : Boot.Tape x.h (2^v.W))
        (late : v.wideFundedHeight≤ x.h) (stockRoom : v.keepLimit*x.w+1≤2^x.h)
        (bounded : x.w≤2^x.h) cost (state : Word (Native.wordBits x.h (2^v.W) Native.copies)) names,
      let P:=v.widePlacement x.h x.w
      let stock:=v.fixedTerminalStock P x.h x.w
      let checkout:=v.wideSignedCheckoutAt x.h x.w size stock v.radius π
        (wideRouteOrder x.h (2^v.W) k) (v.wideFundedRaw x.h x.w v.maxBits raw)
      let report:=v.wide_native_report x.h x.w size π raw v.maxBits extent late stockRoom bounded cost state names
      checkout ((v.privateArena P x.h x.w).endAddress v.mesh)=0 →
        ∀ j : Fin report.edges, report.widthAt j ≤ bound

end

attribute [local irreducible] ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
  CatalystArchive.recordCount CatalystArchive.issued CatalystArchive.nativeSite CatalystArchive.debit

attribute [local irreducible] wide_report_for_dates

-- Read the issued row count and settlement map from the already selected native receipt.

open Lean Elab Tactic in
local elab "applyNativeWidth " cap:ident size:ident extent:ident perm:ident tape:ident accepted:ident report:ident : tactic =>
  withMainContext do
    let localValue (stx : TSyntax `ident) : TacticM Lean.Expr := do
      return ← Meta.getFVarFromUserName stx.getId
    let selected ← Meta.getLocalDeclFromUserName report.getId
    let some value := selected.value? | throwError "expected the selected native report"
    let built ← Meta.whnf value
    unless built.getAppFn.isConstOf ``wide_report_for_dates do throwError "expected the funded dated report"
    let inputs := built.getAppArgs
    let certificate := inputs[inputs.size - 2]!
    let checked ← Meta.whnf (← Meta.inferType certificate)
    unless checked.getAppFn.isConstOf ``Whole.Reconciliation do throwError "expected a native settlement reconciliation"
    let parameters := checked.getAppArgs
    let declaration ← getConstInfo ``Whole.Reconciliation
    let fields ← Meta.forallTelescope declaration.type fun xs _ => do
      let mut fields := #[]
      for name in [`n, `site, `debit, `cj] do
        let some index ← xs.findIdxM? (fun x => return (← x.fvarId!.getDecl).userName == name) |
          throwError "reconciliation has no {name} field"
        fields := fields.push parameters[index]!
      return fields
    let head ← localValue cap
    let fixed ← #[size, extent, perm, tape, accepted].mapM localValue
    let term := mkAppN head ((fixed ++ fields).push certificate)
    (← getMainGoal).assign term
    replaceMainGoal []

/-- The funded native calendar itself supplies the private width bound on its
reported rows, at the original physical row ordinal. -/
theorem cofinal_private_report_rows {κ B : ℝ} (rate : v.sharpPaidUnit≤ unitCost) :
    ∀ᶠ x : Tagged.WideParent κ B in Tagged.WideParent.large κ B,
      v.NativeReportRowsAtMost x (v.widePrivateUnit unitCost * x.w) := by
  refine (v.wideWindow_private_cap (κ:=κ) (B:=B) unitCost rate).mono ?_
  intro x cap size extent π tape late stockRoom bounded cost state names P stock checkout report accepted
  applyNativeWidth cap size extent π tape accepted report


/-- The private bound and its actual paid machine words have a common cofinal cutoff. -/
theorem cofinal_private_word_room {κ B : ℝ} :
    ∀ᶠ x : WideParent κ B in WideParent.large κ B,
      v.widePrivateUnit unitCost*x.w<2^(Native.wordBits x.h (2^v.W) Native.copies) := by
  filter_upwards [WideParent.columnBits_wordBits (κ:=κ) (A:=B) (v.widePrivateUnit unitCost)] with x fit
  exact (WideParent.column_lt _).trans_le (Nat.pow_le_pow_right (by decide) (fit _ _))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows CatalystArchive
open Tagged Tagged.WideStack TaggedShorterBudget TaggedShorterSupergroups ProtocolRAMEmit
open ProtocolRAMReportedPorts PurchaseFrozen
open scoped Classical BigOperators
set_option quotPrecheck false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (tapeSize : ℕ)
    (π : Equiv.Perm (Fin (2^x.h))) (input : Boot.Tape x.h (2^v.W)) (m ell short unitCost : ℕ)
local notation "b" => (v.widePlacement x.h x.w).catalogue
local notation "jobs" => v.wideJobs
local notation "geom" => typeMenu κ A v.W m k jobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geom).menu u δ ξ
local notation "slots" => purchaseSlots x.h v.W k jobs ell
local notation "ports" => WideMemory.H x.h v.W k jobs
local notation "dir" => WideMemory.dir x.h v.W k jobs
local notation "order" => v.wideOrder x.h x.w
local notation "positive" => (b).transport order
local notation "reserve" => fuel v.mesh*x.w
variable (raw : Fin (b).rows→ ProtocolRAMEmit.Row)
    (geometry : Geometry (boardLayout x.h (2^v.W) k x.w reserve) v.radius 1 raw)
    (actual : v.FundedCutRows x.h x.w tapeSize π input raw geometry unitCost)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates x.h v.W k jobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k jobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (kept : geometry.links.Keep (2^x.h)) (lanesFit : v.wideInstalledCap unitCost≤2^ell)
open CoreBoard.PhysicalTerm Tagged.WideControlJoin WideCalendarSites HistoryRoles
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune

local notation "real" => FundedCutRows.installed v x tapeSize π input m ell short unitCost raw geometry actual
  prices pricePos buy groupsFit metadata kept lanesFit
local notation "days" => events v.mesh
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "dst" => TerminalLayout.destination (v.wideSignedPage x.h x.w
  (v.fixedTerminalStock (v.widePlacement x.h x.w) x.h x.w))
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
variable {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (room : cpu.SiteRoom)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
variable (Z : CalendarTerms F x.h (2^v.W) k x.w reserve v.radius 1 slot days (v.wideOrigin x.h x.w size seed))
local notation "D" => v.parentShared x m ell short unitCost ((days).length+1)
local notation "Ex" => OpenPins x.h x.w (Z.nativeRouting D).catalyst
local notation "Se" => Fin (Z.nativeRouting D).selectors
local notation "Priv" => (b).Private order
local notation "cap" => v.widePrivateUnit unitCost*x.w
local notation "lim" => fun _:Priv=>cap
local notation "view" => v.wideHistoryUnit unitCost*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) («W»:=v.W) (k:=k) (attempts:=jobs)
  v.mesh unitCost v.keepLimit (fuel v.mesh) x.w
local notation "history" => Fin (((days).length+1)*Fintype.card
  ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r)))
local notation "outputBits" => ((Fin (dir).groups×Fin ports)×Fin view)
local notation "num" => CalendarTerms.privateWorkspace (geom).index (Equiv.refl Priv) lim roles
  (dir).groups ports (2^ell) ((days).length+1) view x.w
local notation "freeNet" => v.widePrivateGate («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room room.privateBits
local notation "planeNet" => v.widePlane («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room

/-- The original emitted nine-word report survives the paid return. The private
pair and tail tests therefore see the original reported width at every row. -/
theorem FundedCutRows.free (initial before out : Memory W)
    (reported : ∀j,dst≤j→j<dst+9*(b).rows→before j=ProtocolRAMEmit.emitted dst raw initial j)
    (retained : ∀j<(lay).floor,out j=before j)
    (widths : ∀j,(raw j).width≤cap) (fits : cap<2^W) (ex : Ex→Bool) (sel : Se→Bool) :
    ∀(a : ∀t,(Leaf.banks real t).Slots) (y : PrivatePorts lim) (h : history→Bool) (p : outputBits→Bool),
      TypedWiring.value freeNet (CalendarTerms.readPins num ex sel ((G).terminal out)
        (Leaf.write (Leaf.banks real) lim a y h p))=
      if EndsPadded (fun e : Priv=>(raw e.val).width) lim y then Leaf.privateWeight raw positive lim y else 0 := by
  have floorRoom : (lay).floor<2^W := by
    have low : (lay).floor≤(lay).pruneScratch:=Nat.le_add_right _ _
    have last:=cpu.room.original.upper
    omega
  have area:=(v.wideWindow_prune_banks x m ell short u δ ξ unitCost dated floorRoom).1
  intro a y h p
  exact v.wide_private_read x m ell short u δ ξ unitCost cpu.room room.privateBits raw initial out _
    (fun j lo hi=>(retained j (hi.trans_le area)).trans (reported j lo hi))
    (fun _ _=>rfl) (fun e=>widths e.val) fits

/-- The fixed paid OR circuit reads the same real positive banks as the private
test and the original reported plane positions on the common numbering. -/
theorem FundedCutRows.output (out : Memory W) (ex : Ex→Bool) (sel : Se→Bool) :
    ∀(a : ∀t,(Leaf.banks real t).Slots) (y : PrivatePorts lim) (h : history→Bool) (p : outputBits→Bool),
      TypedWiring.value planeNet (CalendarTerms.readPins num ex sel ((G).terminal out)
        (Leaf.write (Leaf.banks real) lim a y h p))=
      TypedWiring.value (Leaf.decoder (F:=F) (groups:=(dir).groups) («ports»:=ports) (lanes:=2^ell)
        («view»:=view) (w:=x.w) (geom).index) (Sum.elim (Leaf.voltage (Leaf.banks real) a) p) :=
  fun a y h p=>v.wide_plane_decode x m ell short u δ ξ unitCost cpu.room (Equiv.refl Priv)
    _ real ex sel ((G).terminal out) a y h p

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
