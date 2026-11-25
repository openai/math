import OAI.Hierarchy.TaggedWideSelectedPreclipReads
import OAI.Hierarchy.TaggedWideCalendarDayOuterBits
import OAI.Hierarchy.TaggedWideSelectedSignedWidths

namespace OAI
/-! # The two bit readings of the selected signed calendar entry -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x) (room : cpu.SiteRoom)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
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
open CoreBoard.HistoryRoles
open StripChart HistoryRoles.RoleProgram ProtocolRAMEmit
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Tagged.PassiveWindow
variable (perm : Equiv.Perm (Tagged.Row x.h)) (height : v.BranchRoleHeight x.h x.w)
local notation "K" => siteLast h d k+1
local notation "bound" => v.wideNeighborCap width unit
local notation "W" => Native.wordBits h d Native.copies
local notation "socket" => shelfSlot («h»:=x.h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "order" => v.wideOrder h width
local notation "board" => v.widePlacement h width
local notation "more" => v.nativeBoards board h width
local notation "arena" => v.privateArena board h width
local notation "rCount" => Fintype.card (Slots h d k)
local notation "offBase" => v.catalystStaticStart board h width
local notation "rowsDeclared" => declaredRows v.mesh (ownerLedger more v.mesh (board).catalogue (board).routes F arena)
local notation "oldStock" => v.fixedTerminalStock board h width
local notation "book" => v.wideSignedPage h width oldStock
local notation "settled" => TerminalLayout.settlement book oldStock
local notation "owners" => sinkBank offBase (rowOnlyCount v.mesh rowsDeclared) rCount (board).catalogue.rows
local notation "wireMemo" => v.wideSignedChart h width oldStock
local notation "keyT" => Bits (CalendarTape.bits sl es) × Fin (es).length
local notation "rawT" t:arg => (reader).format.windows.header es (t).1 seed
local notation "near" t:arg => v.wideOrigin h width S (rawT t) perm
local notation "far" t:arg => checkedOut wireMemo ((arena).endAddress v.mesh) (near t)
local notation "marksT" t:arg => v.birthMarks board h width rCount settled (TerminalLayout.source book)
  (TerminalLayout.table book) (TerminalLayout.destination book) owners (near t)
open private FundedDate.preclipEntriesAt from OAI.Hierarchy.TaggedWireFundedPreclipWidth
local notation "entriesT" key:arg => FundedDate.preclipEntriesAt (v:=v) («h»:=x.h) («width»:=x.w) (size:=S)
  (π:=perm) (rawT key) Sfit height.measure cpu.ready.size_le cpu.ready.credit (0 : Word W)
local notation "idsT" t:arg => timeRows v.sampler perm.symm v.depth (marksT t) (board).catalogue order
  (v.wide_dated_bought_rows h width) (pairKeys (Columns h d) k)
local notation "adT" t:arg => DatedRows.embed v.sampler perm.symm v.depth (marksT t) (board).catalogue order
  (v.wide_dated_bought_rows h width)
local notation "endsT" t:arg => sorted v.sampler perm.symm v.depth (marksT t) ∘ (idsT t)
local notation "lensT" t:arg => v.wideDatedValue h width v.maxBits (near t) (far t) (entriesT t) (t).2.val
  ∘ (adT t) ∘ (idsT t)
private theorem scanMarksExclusive (key : keyT) : Exclusive (marksT key) := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  apply v.paid_days_exclusive
local notation "exclT" key:arg => scanMarksExclusive (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short)
  (u:=u) (δ:=δ) (ξ:=ξ) (cpu:=cpu) (perm:=perm) key
local notation "lblT" t:arg => named v.sampler perm.symm v.depth (marksT t) (exclT t) (idsT t)
local notation "hereT" t:arg => named_coordinate v.sampler perm.symm v.depth (marksT t) (exclT t) (idsT t)
private def datedInputParts (party : Fin K) (V : Widths K) (t : keyT)
    (room : ∀n,(lensT t) n≤bound) (sh : installedWidths (endsT t) (lensT t)=V) :=
  carried (endsT t) (lensT t) party room (PacketNeighbor.localSlot (endsT t) (lensT t) (lblT t) socket (hereT t) party) sh


open CalendarTape
local notation "seedAt" => v.wideOrigin h width S seed perm
variable (conducted : Path sl es seedAt) (observation : Fin (es).length)
local notation "dateKey" => ((encode sl es seedAt conducted, observation) : keyT)
local notation "payShape" => v.widePathRoles h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom conducted unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "signedEnds" => sorted v.sampler perm.symm v.depth (payShape).mark ∘ (payShape).order

attribute [local irreducible] wideDatedValue StockBound.state DatedRows.embed timeRows HistoryRoles.sorted
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "readSignedDateSource"
private def stateRight {n : ℕ} {Fst Snd : Widths n} (_ : Fst=Snd) := Snd
local notation "selectedWidth" => (payShape).atWidth observation.castSucc
local notation "bitRows" => (payShape).bits observation.castSucc
local notation "labels" => named v.sampler perm.symm v.depth (payShape).mark (payShape).exclusive (payShape).order
local notation "coords" => named_coordinate v.sampler perm.symm v.depth (payShape).mark (payShape).exclusive (payShape).order
variable (party : Fin K)
local notation "rowSlot" => PacketNeighbor.localSlot signedEnds bitRows labels socket coords party
local notation "portfolio" room:arg => carried signedEnds bitRows party room rowSlot selectedWidth
private theorem readSignedDateSource (key : keyT) (aligned : key=dateKey)
    (roomKey : ∀n,(lensT key) n ≤ bound) (V : Widths K) (datedWidth : installedWidths (endsT key) (lensT key)=V)
    (roomPath : ∀n,bitRows n ≤ bound) (entryWidth : V=stateRight selectedWidth)
    (state : State (stateRight selectedWidth) party)
    (get : Fin (HistoryRoles.stride k v.sampler.degree v.wideJobs) → Fin bound → Bool)
    (read : ∀i p,(portfolio roomPath).owner i=some p→∀offset:Fin ((portfolio roomPath).width i),
      get i (offset.castLE ((portfolio roomPath).within i))=(state p).val.testBit ((portfolio roomPath).base i+offset.val)) :
    let selected := datedInputParts (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (u:=u) (δ:=δ) (ξ:=ξ)
      (cpu:=cpu) (perm:=perm) (height:=height) party V key roomKey datedWidth
    let seated := cast (congrArg (fun T=>State T party) entryWidth.symm) state
    ∀i p,selected.owner i=some p→∀offset:Fin (selected.width i),
      get i (offset.castLE (selected.within i))=(seated p).val.testBit (selected.base i+offset.val) := by
  subst key
  exact carried_cast_read signedEnds bitRows party roomPath rowSlot selectedWidth state get read entryWidth.symm
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x) (room : cpu.SiteRoom)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
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
open CoreBoard.HistoryRoles
open StripChart HistoryRoles.RoleProgram ProtocolRAMEmit
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Tagged.PassiveWindow
variable (perm : Equiv.Perm (Tagged.Row x.h)) (height : v.BranchRoleHeight x.h x.w)
local notation "K" => siteLast h d k+1
local notation "bound" => v.wideNeighborCap width unit
local notation "W" => Native.wordBits h d Native.copies
local notation "socket" => shelfSlot («h»:=x.h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "order" => v.wideOrder h width
local notation "board" => v.widePlacement h width
local notation "more" => v.nativeBoards board h width
local notation "arena" => v.privateArena board h width
local notation "rCount" => Fintype.card (Slots h d k)
local notation "offBase" => v.catalystStaticStart board h width
local notation "rowsDeclared" => declaredRows v.mesh (ownerLedger more v.mesh (board).catalogue (board).routes F arena)
local notation "oldStock" => v.fixedTerminalStock board h width
local notation "book" => v.wideSignedPage h width oldStock
local notation "settled" => TerminalLayout.settlement book oldStock
local notation "owners" => sinkBank offBase (rowOnlyCount v.mesh rowsDeclared) rCount (board).catalogue.rows
local notation "wireMemo" => v.wideSignedChart h width oldStock
local notation "keyT" => Bits (CalendarTape.bits sl es) × Fin (es).length
local notation "rawT" t:arg => (reader).format.windows.header es (t).1 seed
local notation "near" t:arg => v.wideOrigin h width S (rawT t) perm
local notation "far" t:arg => checkedOut wireMemo ((arena).endAddress v.mesh) (near t)
local notation "marksT" t:arg => v.birthMarks board h width rCount settled (TerminalLayout.source book)
  (TerminalLayout.table book) (TerminalLayout.destination book) owners (near t)
open private FundedDate.preclipEntriesAt from OAI.Hierarchy.TaggedWireFundedPreclipWidth
local notation "entriesT" key:arg => FundedDate.preclipEntriesAt (v:=v) («h»:=x.h) («width»:=x.w) (size:=S)
  (π:=perm) (rawT key) Sfit height.measure cpu.ready.size_le cpu.ready.credit (0 : Word W)
local notation "idsT" t:arg => timeRows v.sampler perm.symm v.depth (marksT t) (board).catalogue order
  (v.wide_dated_bought_rows h width) (pairKeys (Columns h d) k)
local notation "adT" t:arg => DatedRows.embed v.sampler perm.symm v.depth (marksT t) (board).catalogue order
  (v.wide_dated_bought_rows h width)
local notation "endsT" t:arg => sorted v.sampler perm.symm v.depth (marksT t) ∘ (idsT t)
local notation "lensT" t:arg => v.wideDatedValue h width v.maxBits (near t) (far t) (entriesT t) (t).2.val
  ∘ (adT t) ∘ (idsT t)
open CalendarTape
local notation "seedAt" => v.wideOrigin h width S seed perm
variable (conducted : Path sl es seedAt) (observation : Fin (es).length)
local notation "dateKey" => ((encode sl es seedAt conducted, observation) : keyT)
local notation "payShape" => v.widePathRoles h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom conducted unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "signedEnds" => sorted v.sampler perm.symm v.depth (payShape).mark ∘ (payShape).order

attribute [local irreducible] wideDatedValue StockBound.state DatedRows.embed timeRows HistoryRoles.sorted
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "readSignedDateSource"
local notation "selectedWidth" => (payShape).atWidth observation.castSucc
local notation "bitRows" => (payShape).bits observation.castSucc
local notation "labels" => named v.sampler perm.symm v.depth (payShape).mark (payShape).exclusive (payShape).order
local notation "coords" => named_coordinate v.sampler perm.symm v.depth (payShape).mark (payShape).exclusive (payShape).order
variable (party : Fin K)
local notation "rowSlot" => PacketNeighbor.localSlot signedEnds bitRows labels socket coords party
local notation "portfolio" room:arg => carried signedEnds bitRows party room rowSlot selectedWidth
variable (attempt : Attempt) (onDate : (es).get observation=.attempt attempt)
local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "visitAt" => CalendarTape.Prefix.pathVisitAt conducted observation onDate
variable (physicalDate : v.FundedDate h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le (visitAt).prior (visitAt).choice)
local notation "actualDate" => physicalDate
local notation "actualKey" => (((actualDate).code,(actualDate).index) : keyT)
variable (firstWord : ℕ) (issuedInputs : Fin (es).length → Memory W)
  (archived : ∀n,n<(arena).endAddress v.mesh → issuedInputs (actualDate).index n=(far actualKey) n)
  (floor : v.wideSpillSheetHeight ≤ h) (V : Widths K)
  (roomOnDate : ∀n,(lensT actualKey) n≤bound) (shapeOnDate : installedWidths (endsT actualKey) (lensT actualKey)=V)

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "inputReadAtFundedDate"
include roomOnDate in
private theorem inputReadAtFundedDate (aligned : actualKey = dateKey)
    (roomPath : ∀lane,bitRows lane ≤ bound) (entryWidth : V=stateRight selectedWidth)
    (state : State (stateRight selectedWidth) party)
    (fetch : Fin (HistoryRoles.stride k v.sampler.degree v.wideJobs) → Fin bound → Bool)
    (observed : ∀lane peer,(portfolio roomPath).owner lane=some peer →
      ∀offset:Fin ((portfolio roomPath).width lane),
        fetch lane (offset.castLE ((portfolio roomPath).within lane))=
          (state peer).val.testBit ((portfolio roomPath).base lane+offset.val)) :
    let partition := (actualDate).signedInputParts Sfit height firstWord issuedInputs unit v.calendarUnit_rate
      floor archived party V shapeOnDate
    let seated := cast (congrArg (fun T=>State T party) entryWidth.symm) state
    ∀lane peer, partition.owner lane=some peer → ∀offset : Fin (partition.width lane),
      fetch lane (offset.castLE (partition.within lane))=(seated peer).val.testBit (partition.base lane+offset.val) :=
  readSignedDateSource (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (u:=u) (δ:=δ) (ξ:=ξ)
    (cpu:=cpu) (perm:=perm) (height:=height) (conducted:=conducted) (observation:=observation) (party:=party)
    actualKey aligned roomOnDate V shapeOnDate roomPath entryWidth state fetch observed
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

section
open Lean Elab Term in
local elab "paidSourceCoordinates% " subject:ident " through " stopBinder:ident " with "
    "[" coords:(ident " := " term),* "]" : term => do
  let declaredSubject ← resolveGlobalConstNoOverload subject
  let decl ← getConstInfo declaredSubject
  let vArg ← Meta.getFVarFromUserName `v
  let descriptor := (← Meta.inferType vArg).consumeMData.getAppArgs
  let mut known : Std.HashMap Name Lean.Expr := {}
  for item in coords.getElems do
    known := known.insert item.raw[0].getId.eraseMacroScopes (← elabTerm item.raw[2] none)
  let mut declaredArguments := #[]
  let mut typ := decl.type
  let mut finished := false
  while typ.isForall do
    let binder := typ.bindingName!.eraseMacroScopes
    let arg ← if declaredArguments.size < descriptor.size then pure descriptor[declaredArguments.size]!
      else if let some supplied := known[binder]? then pure supplied
      else if typ.bindingInfo! == .instImplicit then pure descriptor[1]!
      else Meta.getFVarFromUserName binder
    declaredArguments := declaredArguments.push arg
    if binder == stopBinder.getId then
      finished := true
      break
    typ := typ.bindingBody!
  unless finished do throwError "missing selected physical binder {stopBinder.getId}"
  return mkAppN (mkConst declaredSubject (decl.levelParams.map Level.param)) declaredArguments

open Lean Elab Term in
local elab "earnedWidthEndpoint% " evidence:term:max : term => do
  let fact ← elabTerm evidence none
  let some eq ← Meta.whnfUntil (← Meta.inferType fact) ``Eq | throwError "expected the physical width equality"
  return eq.getAppArgs[2]!



noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Lean Meta Elab Term in
local elab "purchasedInputRead% " transportRule:ident " at " actualParts:term:max
    " dated " datePair:term:max " bounded " dateBounds:term:max : term => do
  let selected ← elabTerm actualParts none
  let keyed ← elabTerm datePair none
  let bounds ← elabTerm dateBounds none
  let some issued ← whnfUntil selected ``FundedDate.signedInputParts
    | throwError "the selected partition must be the physical dated input"
  let mut fields : Std.HashMap Name Lean.Expr := {}
  for evidence in #[issued,selected] do
    let info ← getConstInfo evidence.getAppFn.constName!
    let mut tab := info.type
    for x in evidence.getAppArgs do
      unless tab.isForall do break
      fields := fields.insert tab.bindingName!.eraseMacroScopes x
      tab := tab.bindingBody!
  -- The selected wrapper returns a function after the archived argument.
  -- The final three paid site arguments belong to the physical declaration.
  let theoremName ← resolveGlobalConstNoOverload transportRule
  let thm ← getConstInfo theoremName
  let signedRoom := Lean.Expr.proj ``And 0 bounds
  let mut result : Array Lean.Expr := #[]
  let mut rule := thm.type
  let aliases : List (Name × Name) := [(`conducted,`j),(`observation,`t),(`party,`site),
    (`attempt,`a),(`physicalDate,`J),(`firstWord,`first),(`issuedInputs,`input),(`floor,`large),(`V,`active),(`shapeOnDate,`shape)]
  let formatArgs := (← inferType (← getFVarFromUserName `v)).consumeMData.getAppArgs
  while rule.isForall do
    let name := rule.bindingName!.eraseMacroScopes
    if name == `roomPath then break
    let matched := (aliases.lookup name).getD name
    let arg ← if name == `aligned then pure keyed
      else if name == `roomOnDate then pure signedRoom
      else if rule.bindingInfo! == .instImplicit then pure formatArgs[1]!
      else if let some value := fields[matched]? then pure value
      else getFVarFromUserName name
    result := result.push arg
    rule := rule.bindingBody!
  unless rule.isForall && rule.bindingName!.eraseMacroScopes == `roomPath do throwError "the funded read must expose the chronological row bounds"
  return mkAppN (mkConst theoremName (thm.levelParams.map Level.param)) result

private theorem splicePhysicalDatePair {L R : Type} {a₁ a₂ : L} {b₁ b₂ : R}
    (observation : a₁=a₂ ∧ b₁=b₂) : (a₁,b₁)=(a₂,b₂) := Prod.ext observation.1 observation.2

open Lean Meta Elab Term in
local elab "collectedDatePair% " recordedTerm:term:max : term => do
  let proofTerm ← elabTerm recordedTerm none
  let some conj ← whnfUntil (← inferType proofTerm) ``And | throwError "expected the two recorded date coordinates"
  let some leftEq ← whnfUntil conj.getAppArgs[0]! ``Eq | throwError "expected the calendar code equality"
  let some rightEq ← whnfUntil conj.getAppArgs[1]! ``Eq | throwError "expected the paid date equality"
  let la := leftEq.getAppArgs
  let ra := rightEq.getAppArgs
  return mkAppN (mkConst ``splicePhysicalDatePair) #[la[0]!,ra[0]!,la[1]!,la[2]!,ra[1]!,ra[2]!,proofTerm]

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open TaggedPrune CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x)
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
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
variable (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
variable {b : Fin k→ℕ} (e : OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unit g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
variable (height : v.BranchRoleHeight h width) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

variable (routeAge : v.routingHeight ≤ x.h) (s : Fin (siteLast x.h (2^v.W) k+1))
local notation "inWidth" => paidSourceCoordinates% selected_signed_input_width through routeAge with [unitCost := unit]
local notation "beforeParts" => paidSourceCoordinates% selectedSignedInputParts through shape with
  [unitCost := unit, rate := v.calendarUnit_rate, site := s, active := (earnedWidthEndpoint% inWidth), shape := inWidth]
local notation "paidBounds" => paidSourceCoordinates% selectedSignedRowBounds through onDate with [unitCost := unit, rate := v.calendarUnit_rate]
local notation "paidCode" => paidSourceCoordinates% selectedPreclipCode through onDate with [unitCost := unit]
set_option hygiene false in
local notation "paidInputProof" => purchasedInputRead% inputReadAtFundedDate at beforeParts
  dated (collectedDatePair% paidCode) bounded paidBounds

/-- The physical signed aperture of this selected path accepts the bit reading of
its chronological source, with the recorded input-state width identification. -/
private theorem selectedPaidInputRead : type_of% paidInputProof :=
  no_implicit_lambda% paidInputProof

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Lean Meta Elab Term in
local elab "selectedSourceFromTimed% " datedRule:term:max physicalRead:term:max entryEq:term:max : term => do
  let rule ← elabTerm datedRule none
  let timed ← elabTerm physicalRead none
  let alignment ← elabTerm entryEq none
  let mut timing ← inferType timed
  while let .letE _ _ v b _ := timing do timing := b.instantiate1 v
  forallTelescope timing fun xs eqn => do
    unless xs.size == 4 && eqn.isAppOf ``Eq do throwError "expected the four occupied dated bit binders"
    let rhs := eqn.getAppArgs[2]!.headBeta
    unless rhs.isAppOf ``Nat.testBit do throwError "expected the chronological state bit"
    let value := rhs.getAppArgs[0]!
    let appliedState ← if value.isProj then pure value.projExpr!
      else if value.isAppOf ``Fin.val then pure value.appArg!
      else throwError "expected the physical state value"
    unless appliedState.isApp && appliedState.appArg! == xs[1]! do throwError "expected the occupied neighboring state"
    let state := appliedState.appFn!
    let occupied ← inferType xs[2]!
    unless occupied.isAppOf ``Eq do throwError "expected the occupied partition proof"
    let namedPort := occupied.getAppArgs[1]!
    unless namedPort.isApp && namedPort.appArg! == xs[0]! do throwError "expected the named port at this lane"
    let portAccessor := namedPort.appFn!
    let actualParts := if portAccessor.isProj then portAccessor.projExpr! else portAccessor.appArg!
    let some carry ← whnfUntil actualParts ``Tagged.PassiveWindow.carried | throwError "expected the chronological carried rows"
    let ca := carry.getAppArgs
    let room := ca[ca.size-4]!
    let lhs := eqn.getAppArgs[1]!.headBeta
    unless lhs.isAppOf ``Sum.elim do throwError "expected the actual calendar gate assignment"
    let physicalWire := lhs.appArg!
    unless physicalWire.isApp && physicalWire.appFn!.isApp && physicalWire.appFn!.appArg! == xs[0]! do throwError "expected the substep word and lane"
    let capType ← inferType physicalWire.appArg!
    let fetch ← withLocalDeclD `wireDigit capType fun wireDigit =>
      mkLambdaFVars #[xs[0]!,wireDigit] (mkApp lhs.appFn! (mkApp2 physicalWire.appFn!.appFn! xs[0]! wireDigit))
    return mkAppN rule #[room,alignment,state,fetch,timed]

open Lean Meta Elab Term in
local elab "selectedEntryType% " paidRule:term:max : term => do
  let issued ← elabTerm paidRule none
  let ts ← whnf (← inferType issued)
  let .forallE room _ next _ := ts | throwError "expected the dated source capacity"
  let .forallE entry entryType _ _ := next | throwError "expected the original state-width equality"
  unless room.eraseMacroScopes == `roomPath && entry.eraseMacroScopes == `entryWidth && !entryType.hasLooseBVars do
    throwError "the original paid state width must be independent of the capacity proof"
  return entryType

open Lean Meta Elab Term in
local elab "selectedSourceStatement% " compare:term:max selected:term:max : term => do
  let owned ← elabTerm selected none
  let proof ← elabTerm compare none
  let .letE pn pt _ later pnU ← inferType proof | throwError "expected the physical signed partition"
  let .letE _ _ state bits _ := later | throwError "expected the transported original state"
  unless state.isAppOf ``cast && bits.isForall do throwError "expected the chronological bit equality"
  return .letE pn pt owned later pnU

open Lean Elab Tactic in
local elab "acceptSourceCalendarRead " value:term:max : tactic => withMainContext do
  let base ← Term.elabTerm value none
  (← getMainGoal).assign (← instantiateMVars base)
  replaceMainGoal []

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option cleanup.letToHave false
run_cmd do
  for n in ["selectedSignedSourceFromDate"] do
    Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env n
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
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

variable (routeAge : v.routingHeight≤x.h)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "Z" => v.routedSchedule h width S arenaRoom seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit routeAge support.size.widthFloor support.size.words
local notation "rout" => (Z).nativeRouting D
local notation "sites" => SignedSites.ofCalendar (cpu:=cpu) Z control v.calendarTerminalWidth
  (v.calendarTerminalPins x m ell short)
local notation "source" => fun _ : Fin (m+1)=>slots
local notation "count" => purchaseModules v.W u δ ξ menu x
local notation "target" => fun i=>purchaseCandidates h v.W k v.wideJobs slots ((menu).height i x) (count i)
local notation "Buy" => PurchaseList (F:=F) (C:=C) menu x source target count
local notation "Ex" => OpenPins h width (rout).catalyst
local notation "report" π:arg j:arg => v.wide_reported_path h width S π seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words j
variable (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
variable (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
local notation "path" => (Fintype.equivFin (Path sl es (base perm))).symm i
local notation "record" => CalendarTape.encode sl es (base perm) path

open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.BranchRoles Tagged.WideCalendarSites
open StripChart HistoryRoles.RoleProgram ProtocolRAMEmit
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open Tagged.WideStack.Leaf ProtocolRAMReportedPorts
variable (height : v.BranchRoleHeight h width)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unit cpu.room).2
local notation "W" => Native.wordBits h d Native.copies
local notation "root" => (CalendarTape.Prefix.start : CalendarTape.Prefix sl es (base perm) es (base perm))
local notation "tree" => CalendarTape.Prefix.cursorSlot (slot:=sl) (events:=es) (x₀:=base perm)
local notation "ws" => CalendarTape.Prefix.atWidth ((Z).width perm)
local notation "top" => CalendarTape.Prefix.atCursor root
local notation "branch" => CalendarTape.Prefix.histories root path
local notation "stop" => terminal tree es top branch
local notation "input" => (reader).format.windows.header es record seed
local notation "bill" => v.wide_reported_path_native h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words path
local notation "admitted" => (bill).choose
local notation "cost" => (bill).choose_spec.choose
local notation "names" => (bill).choose_spec.choose_spec.choose
local notation "accepted" => (bill).choose_spec.choose_spec.choose_spec.1
local notation "native" => v.wide_native_report h width S perm.symm input v.maxBits Sfit admitted
  cpu.ready.credit cpu.ready.size_le cost (0:Word W) names
local notation "runAt" => v.wide_selected_local_return m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "out" => (runAt).2.2.2.choose
local notation "actual" => Classical.choice (support.funding S Sfit perm.symm input admitted cpu.ready.credit
  cpu.ready.size_le cost (0:Word W) names accepted)
local notation "install" ok:arg => FundedCutRows.rowData v x S perm.symm input m ell short unit (native).rows
  (native).geometry actual prices pricePos buy groupsFit metadata ok lanesFit
local notation "geom" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "dir" => WideMemory.dir h v.W k v.wideJobs
local notation "ports" => WideMemory.H h v.W k v.wideJobs
local notation "b" => (v.widePlacement h width).catalogue
local notation "order" => v.wideOrder h width
local notation "roles" => HistoryRoles.ceiling v.sampler («h»:=x.h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unit v.keepLimit (fuel v.mesh) width
local notation "view" => v.wideHistoryUnit unit*width
local notation "times" => ((es).length+1)*Fintype.card ((r:Public v.sampler h v.W k v.wideJobs)×Fin (roles r))
local notation "shape" => v.widePathRoles h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "pins" => v.widePathCells h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "place" => timelineFin tree ws pins es top branch
local notation "replayed" => cursorReport perm ((Z).width perm) ((Z).reported perm) branch
local notation "Rpt" => CoreBoard.Report perm d k width (fuel v.mesh*width) v.radius 1 (ws stop)
local notation "table" r:arg => (⟨(r).edges,(r).rows⟩ : CalendarTerms.RowBoard)
local notation "plan" r:arg => CalendarTerms.RankedRows (F:=F) (geom).index D (dir).groups ports (2^ell) width m times view (table r)

local notation "same" => v.wide_selected_geometry m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "sameRows" => congrArg (fun r:RowGeometry h d k width (fuel v.mesh*width) v.radius 1=>
  (⟨r.1,r.2.1⟩:CalendarTerms.RowBoard)) same
local notation "kept" => (native).geometry.links.Keep (2^h)
local notation "recorded" => v.wideCalendarPartyPlace m ell short u δ ξ x cpu Z perm i height (fun _=>rfl)
local notation "rnk" ok:arg => CalendarTerms.RankedRows.onBranch Z perm i sameRows (install ok)
local notation "wordTable" => (r : Fin (replayed).edges)→Fin (2^((replayed).rows r).width)
local notation "states" => SiteChoices tree ws es top branch

local notation "data" ok:arg words:arg q:arg => v.calendarDayPins (C:=C) m ell short u δ ξ x cpu support routeAge
  prices pricePos groupsFit metadata lanesFit buy e perm i tag height ok words q

open LinearAlgebra.SpectralBooks.SiteTensor Tagged.PassiveWindow
local notation "K" => siteLast h d k+1
local notation "deg" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "bound" => v.wideNeighborCap width unit
local notation "ends" => sorted v.sampler perm.symm v.depth (shape).mark ∘ (shape).order
local notation "portsAt" => named v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order
local notation "socket" => shelfSlot («h»:=x.h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "here" => named_coordinate v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order
local notation "timer" => SignedSites.calendarTime (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unit)
local notation "boundAt" => v.wide_outer_lane h width unit
variable (ok : kept) (words : wordTable) (q : states) (j : Fin (es).length) (s : Fin K) (right : Bool)
local notation "timeAt" => if right then j.succ else j.castSucc
local notation "bits" => (shape).bits timeAt
local notation "fits" => fun r=>((shape).fits timeAt r false).trans (boundAt (portsAt (r,false)))
local notation "slotAt" => PacketNeighbor.localSlot ends bits portsAt socket here s
local notation "chart" => (shape).atWidth timeAt
local notation "parts" => carried ends bits s fits slotAt chart
local notation "current" => datedState tree ws s es top branch timeAt (q s)
local notation "assignment" => data ok words q
local notation "value" => Sum.elim e (Sum.elim record (Sum.elim assignment ((G).terminal out)))
local notation "tap" => LedgerStep.outerWord (cap:=bound) G es roles socket timer j s right

open WireTelescope.NamedAperture
variable (a : Attempt) (onDate : (es).get j=.attempt a)
local notation "chosenAt" => CalendarTape.Prefix.pathVisitAt path j onDate
local notation "dte" => v.wide_funded_date_with h width S arenaRoom perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosenAt).prior (chosenAt).choice (chosenAt).future
local notation "codeAt" => v.selectedPreclipCode m ell short u δ ξ unit x cpu perm path j a onDate
local notation "inWidth" => paidSourceCoordinates% selected_signed_input_width through routeAge with
  [unitCost := unit, j := path, t := j]
local notation "offerWidth" => v.selected_signed_offer_width m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path height j a onDate routeAge
local notation "beforeParts" => paidSourceCoordinates% selectedSignedInputParts through «shape» with
  [unitCost := unit, rate := v.calendarUnit_rate, «b» := (rout).catalyst, j := path, t := j,
   site := s, active := (earnedWidthEndpoint% inWidth), «shape» := inWidth]
local notation "afterParts" => v.selectedSignedOfferParts m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path height j a onDate s _ offerWidth
local notation "Gdata" z:arg => Sum.elim e (Sum.elim record (Sum.elim (Sum.elim assignment z) ((G).terminal out)))
local notation "wireAt" side:arg => LedgerStep.substepWord (cap:=bound) G es roles socket timer j s false side
local notation "cellChart" => v.selected_preclip_layout m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path routeAge height j a onDate
local notation "cellSite" => v.selected_preclip_site m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path routeAge height j a onDate
local notation "middle" z:arg => LedgerStep.middle s (LedgerStep.siteChart cellChart cellSite s) z

local notation "datedRule" => paidSourceCoordinates% selectedPaidInputRead through s with [«b» := (rout).catalyst, j := path, t := j]
local notation "dataBefore" => datedState tree ws s es top branch j.castSucc (q s)
local notation "chartBefore" => (shape).atWidth j.castSucc
local notation "lensBefore" => (shape).bits j.castSucc
local notation "roomBefore" => fun r=>((shape).fits j.castSucc r false).trans (boundAt (portsAt (r,false)))
local notation "slotBefore" => PacketNeighbor.localSlot ends lensBefore portsAt socket here s

/-- Apply the selected physical source rule to the recorded calendar substep. -/
private theorem selectedSignedSourceFromDate (entry : selectedEntryType% datedRule)
    (mid : Fin (deg*bound)→Bool)
    (read : let origParts := carried ends lensBefore s roomBefore slotBefore chartBefore
      ∀lane party,origParts.owner lane=some party→∀bitNo : Fin (origParts.width lane),
        Sum.elim (Gdata mid) id ((wireAt false) lane (bitNo.castLE (origParts.within lane)))=
          (dataBefore party).val.testBit (origParts.base lane+bitNo.val)) :
    selectedSourceStatement% (selectedSourceFromTimed% datedRule read entry) beforeParts := by
  acceptSourceCalendarRead (selectedSourceFromTimed% datedRule read entry)


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
open Lean Meta Elab Command in
local elab "settleDatedSource " original:ident " from " selectedRule:ident " via " timedRead:ident : command => do
  let resultName := (← getCurrNamespace) ++ original.getId.eraseMacroScopes
  modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env resultName.getString!
  runTermElabM fun _ => do
    let ruleName ← resolveGlobalConstNoOverload selectedRule
    let temporalName ← resolveGlobalConstNoOverload timedRead
    let selected ← getConstInfo ruleName
    let recorded ← getConstInfo temporalName
    let mut remaining := selected.type
    let mut names : Array Name := #[]
    while remaining.isForall && remaining.bindingName!.eraseMacroScopes != `read do
      names := names.push remaining.bindingName!.eraseMacroScopes
      remaining := remaining.bindingBody!
    unless remaining.isForall && remaining.bindingName!.eraseMacroScopes == `read do
      throwError "the signed state rule must end with its chronological read"
    let parameters := selected.levelParams.map Level.param
    let (closedType,closedValue) ← forallBoundedTelescope selected.type (some names.size) fun xs pending => do
      let mut physical : Std.HashMap Name Lean.Expr := {}
      for (n,x) in names.zip xs do physical := physical.insert n x
      let mut checked : Array Lean.Expr := #[]
      let mut ts := recorded.type
      while ts.isForall do
        let n := ts.bindingName!.eraseMacroScopes
        let x ← if checked.size < 8 then pure xs[checked.size]!
          else if n == `right then pure (mkConst ``Bool.false)
          else if let some x := physical[n]? then pure x
          else throwError "missing selected parameter {n} in the dated read"
        checked := checked.push x
        if n == `mid then break
        ts := ts.bindingBody!
      unless ts.isForall && ts.bindingName!.eraseMacroScopes == `mid do
        throwError "the dated calendar must accept the actual intermediate word"
      let receipt := mkAppN (mkConst temporalName (recorded.levelParams.map Level.param)) checked
      let proof := mkApp (mkAppN (mkConst ruleName parameters) xs) receipt
      let result := pending.bindingBody!.instantiate1 receipt
      return (← mkForallFVars xs result, ← mkLambdaFVars xs proof)
    let shared := ShareCommon.shareCommon' #[closedType,closedValue]
    if shared.any fun e => e.hasFVar || e.hasMVar || e.hasSorry then throwError "the closed source requires all physical arguments"
    addDecl (.thmDecl {name := resultName, levelParams := selected.levelParams, type := shared[0]!, value := shared[1]!})

settleDatedSource selected_signed_source_bits from selectedSignedSourceFromDate via wide_calendar_day_substep_carried_bits

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option cleanup.letToHave false
run_cmd do
  for n in ["selected_signed_source_bits", "selected_signed_target_bits"] do
    Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env n
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ v.calendarUnit N x)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ v.calendarUnit v.calendarUnit_rate x)
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

variable (routeAge : v.routingHeight≤x.h)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "Z" => v.routedSchedule h width S arenaRoom seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit routeAge support.size.widthFloor support.size.words
local notation "rout" => (Z).nativeRouting D
local notation "sites" => SignedSites.ofCalendar (cpu:=cpu) Z control v.calendarTerminalWidth
  (v.calendarTerminalPins x m ell short)
local notation "source" => fun _ : Fin (m+1)=>slots
local notation "count" => purchaseModules v.W u δ ξ menu x
local notation "target" => fun i=>purchaseCandidates h v.W k v.wideJobs slots ((menu).height i x) (count i)
local notation "Buy" => PurchaseList (F:=F) (C:=C) menu x source target count
local notation "Ex" => OpenPins h width (rout).catalyst
local notation "report" π:arg j:arg => v.wide_reported_path h width S π seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words j
variable (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
variable (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
local notation "path" => (Fintype.equivFin (Path sl es (base perm))).symm i
local notation "record" => CalendarTape.encode sl es (base perm) path

open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.BranchRoles Tagged.WideCalendarSites
open StripChart HistoryRoles.RoleProgram ProtocolRAMEmit
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open Tagged.WideStack.Leaf ProtocolRAMReportedPorts
variable (height : v.BranchRoleHeight h width)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unit cpu.room).2
local notation "W" => Native.wordBits h d Native.copies
local notation "root" => (CalendarTape.Prefix.start : CalendarTape.Prefix sl es (base perm) es (base perm))
local notation "tree" => CalendarTape.Prefix.cursorSlot (slot:=sl) (events:=es) (x₀:=base perm)
local notation "ws" => CalendarTape.Prefix.atWidth ((Z).width perm)
local notation "top" => CalendarTape.Prefix.atCursor root
local notation "branch" => CalendarTape.Prefix.histories root path
local notation "stop" => terminal tree es top branch
local notation "input" => (reader).format.windows.header es record seed
local notation "bill" => v.wide_reported_path_native h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words path
local notation "admitted" => (bill).choose
local notation "cost" => (bill).choose_spec.choose
local notation "names" => (bill).choose_spec.choose_spec.choose
local notation "accepted" => (bill).choose_spec.choose_spec.choose_spec.1
local notation "native" => v.wide_native_report h width S perm.symm input v.maxBits Sfit admitted
  cpu.ready.credit cpu.ready.size_le cost (0:Word W) names
local notation "runAt" => v.wide_selected_local_return m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "out" => (runAt).2.2.2.choose
local notation "actual" => Classical.choice (support.funding S Sfit perm.symm input admitted cpu.ready.credit
  cpu.ready.size_le cost (0:Word W) names accepted)
local notation "install" ok:arg => FundedCutRows.rowData v x S perm.symm input m ell short unit (native).rows
  (native).geometry actual prices pricePos buy groupsFit metadata ok lanesFit
local notation "geom" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "dir" => WideMemory.dir h v.W k v.wideJobs
local notation "ports" => WideMemory.H h v.W k v.wideJobs
local notation "b" => (v.widePlacement h width).catalogue
local notation "order" => v.wideOrder h width
local notation "roles" => HistoryRoles.ceiling v.sampler («h»:=x.h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unit v.keepLimit (fuel v.mesh) width
local notation "view" => v.wideHistoryUnit unit*width
local notation "times" => ((es).length+1)*Fintype.card ((r:Public v.sampler h v.W k v.wideJobs)×Fin (roles r))
local notation "shape" => v.widePathRoles h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "pins" => v.widePathCells h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)
local notation "place" => timelineFin tree ws pins es top branch
local notation "replayed" => cursorReport perm ((Z).width perm) ((Z).reported perm) branch
local notation "Rpt" => CoreBoard.Report perm d k width (fuel v.mesh*width) v.radius 1 (ws stop)
local notation "table" r:arg => (⟨(r).edges,(r).rows⟩ : CalendarTerms.RowBoard)
local notation "plan" r:arg => CalendarTerms.RankedRows (F:=F) (geom).index D (dir).groups ports (2^ell) width m times view (table r)

local notation "same" => v.wide_selected_geometry m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "sameRows" => congrArg (fun r:RowGeometry h d k width (fuel v.mesh*width) v.radius 1=>
  (⟨r.1,r.2.1⟩:CalendarTerms.RowBoard)) same
local notation "kept" => (native).geometry.links.Keep (2^h)
local notation "recorded" => v.wideCalendarPartyPlace m ell short u δ ξ x cpu Z perm i height (fun _=>rfl)
local notation "rnk" ok:arg => CalendarTerms.RankedRows.onBranch Z perm i sameRows (install ok)
local notation "wordTable" => (r : Fin (replayed).edges)→Fin (2^((replayed).rows r).width)
local notation "states" => SiteChoices tree ws es top branch

local notation "data" ok:arg words:arg q:arg => v.calendarDayPins (C:=C) m ell short u δ ξ x cpu support routeAge
  prices pricePos groupsFit metadata lanesFit buy e perm i tag height ok words q

open LinearAlgebra.SpectralBooks.SiteTensor Tagged.PassiveWindow
local notation "K" => siteLast h d k+1
local notation "deg" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "bound" => v.wideNeighborCap width unit
local notation "ends" => sorted v.sampler perm.symm v.depth (shape).mark ∘ (shape).order
local notation "portsAt" => named v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order
local notation "socket" => shelfSlot («h»:=x.h) («W»:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "here" => named_coordinate v.sampler perm.symm v.depth (shape).mark (shape).exclusive (shape).order
local notation "timer" => SignedSites.calendarTime (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unit)
local notation "boundAt" => v.wide_outer_lane h width unit
variable (ok : kept) (words : wordTable) (q : states) (j : Fin (es).length) (s : Fin K) (right : Bool)
local notation "timeAt" => if right then j.succ else j.castSucc
local notation "bits" => (shape).bits timeAt
local notation "fits" => fun r=>((shape).fits timeAt r false).trans (boundAt (portsAt (r,false)))
local notation "slotAt" => PacketNeighbor.localSlot ends bits portsAt socket here s
local notation "chart" => (shape).atWidth timeAt
local notation "parts" => carried ends bits s fits slotAt chart
local notation "current" => datedState tree ws s es top branch timeAt (q s)
local notation "assignment" => data ok words q
local notation "value" => Sum.elim e (Sum.elim record (Sum.elim assignment ((G).terminal out)))
local notation "tap" => LedgerStep.outerWord (cap:=bound) G es roles socket timer j s right

open WireTelescope.NamedAperture
variable (a : Attempt) (onDate : (es).get j=.attempt a)
local notation "chosenAt" => CalendarTape.Prefix.pathVisitAt path j onDate
local notation "dte" => v.wide_funded_date_with h width S arenaRoom perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosenAt).prior (chosenAt).choice (chosenAt).future
local notation "codeAt" => v.selectedPreclipCode m ell short u δ ξ unit x cpu perm path j a onDate
open Lean Elab Term in
local elab "paidOfferWidth% " evidence:term:max : term => do
  let fact ← elabTerm evidence none
  let some eq ← Meta.whnfUntil (← Meta.inferType fact) ``Eq | throwError "expected the physical width equality"
  return eq.getAppArgs[2]!


open Lean Elab Term in
local elab "selectedBitOp% " op:ident "[" args:term:max,* "]" : term => do
  let format ← Meta.getFVarFromUserName `v
  let mut xs := (← Meta.inferType format).consumeMData.getAppArgs
  unless xs.size == 8 do throwError "expected the physical protocol parameters"
  for arg in args.getElems do
    xs := xs.push (← instantiateMVars (← elabTerm arg none))
  let name ← realizeGlobalConstNoOverloadWithInfo op
  let fn ← Meta.mkConstWithFreshMVarLevels name
  return mkAppN fn xs

local notation "inWidth" => v.selected_signed_input_width (m:=m) (ell:=ell) (short:=short) (u:=u) (δ:=δ) (ξ:=ξ)
  (unitCost:=unit) (x:=x) (cpu:=cpu) (perm:=perm) (j:=path) (height:=height) (t:=j) (a:=a)
  (onDate:=onDate) (routeAge:=routeAge)
local notation "offerWidth" => selectedBitOp% selected_signed_offer_width [κ,A,v,m,ell,short,u,δ,ξ,unit,N,x,cpu,v.calendarUnit_rate,support,prices,C,pricePos,buy,groupsFit,metadata,lanesFit,(rout).catalyst,e,perm,tag,path,height,j,a,onDate,routeAge]
local notation "beforeParts" => v.selectedSignedInputParts m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path height j a onDate s _ inWidth
local notation "afterParts" => selectedBitOp% selectedSignedOfferParts [κ,A,v,m,ell,short,u,δ,ξ,unit,N,x,cpu,v.calendarUnit_rate,support,prices,C,pricePos,buy,groupsFit,metadata,lanesFit,(rout).catalyst,e,perm,tag,path,height,j,a,onDate,s,(paidOfferWidth% offerWidth),offerWidth]
local notation "Gdata" z:arg => Sum.elim e (Sum.elim record (Sum.elim (Sum.elim assignment z) ((G).terminal out)))
local notation "wireAt" side:arg => LedgerStep.substepWord (cap:=bound) G es roles socket timer j s false side
local notation "cellChart" => selectedBitOp% selected_preclip_layout [κ,A,v,m,ell,short,u,δ,ξ,unit,N,x,cpu,v.calendarUnit_rate,support,prices,C,pricePos,buy,groupsFit,metadata,lanesFit,(rout).catalyst,e,perm,tag,path,routeAge,height,j,a,onDate]
local notation "cellSite" => selectedBitOp% selected_preclip_site [κ,A,v,m,ell,short,u,δ,ξ,unit,N,x,cpu,v.calendarUnit_rate,support,prices,C,pricePos,buy,groupsFit,metadata,lanesFit,(rout).catalyst,e,perm,tag,path,routeAge,height,j,a,onDate]
local notation "middle" z:arg => LedgerStep.middle s (LedgerStep.siteChart cellChart cellSite s) z

private def layoutDomain {n len : ℕ} {B : Widths n} (_ : (Σs,SiteBit B s) ↪ Fin n×Fin len) := B

local notation "selectedOfferEvidence" payload:arg => selectedBitOp% calendar_day_offer_read [κ,A,C,v,m,ell,short,u,δ,ξ,N,x,cpu,support,
    routeAge,prices,pricePos,groupsFit,metadata,lanesFit,buy,e,perm,i,tag,height,ok,words,q,j,s,
    a,onDate,false,(payload),(paidOfferWidth% offerWidth),offerWidth]

-- The calendar read exposes the same three data values as the selected read:
-- its carried partition, its state after transport, and its gate assignment.
-- Keep the paid assignment and all four occupied-bit binders from that theorem.
-- Supply the partition of the elected wire and the recorded state equality.
open Lean Meta Elab Term in
local elab "selectedOfferStatement% " observed:term:max partition:term:max alignment:term:max : term => do
  let receipt ← elabTerm observed none
  let selectedParts ← elabTerm partition none
  let widthEq ← elabTerm alignment none
  let eqType ← inferType widthEq
  let #[widthType, afterWidth, centerWidth] := eqType.getAppArgs | throwError "expected the placement width equality"
  unless eqType.isAppOf ``Eq do throwError "expected the placement width equality"
  let toActive := mkAppN (mkConst ``Eq.symm eqType.getAppFn.constLevels!) #[widthType, afterWidth, centerWidth, widthEq]
  let .letE partName partType _ stateBody partUnused ← inferType receipt
    | throwError "expected the paid partition in the calendar read"
  let .letE stateName stateType oldState gateBody stateUnused := stateBody
    | throwError "expected the transported calendar state"
  let .letE gateName gateType gateValue bitRows gateUnused := gateBody | throwError "expected the calendar gate assignment"
  let .forallE laneName laneType parties laneInfo := bitRows | throwError "expected the selected lane"
  let .forallE partyName partyType hits partyInfo := parties | throwError "expected its occupied port"
  let .forallE hitName hitType offsets hitInfo := hits | throwError "expected its owner equation"
  let .forallE _ offsetType equality offsetInfo := offsets | throwError "expected a bit of the occupied interval"
  let namedRows := Expr.forallE laneName laneType (.forallE partyName partyType
    (.forallE hitName hitType (.forallE `u offsetType equality offsetInfo) hitInfo) partyInfo) laneInfo
  let selectedGate := Expr.letE gateName gateType gateValue namedRows gateUnused
  unless gateValue.isAppOf ``Sum.elim && bitRows.isForall do throwError "expected a site-indexed calendar read"
  let #[fromState,toState,transport,datum] := oldState.getAppArgs | throwError "expected a state cast"
  unless oldState.isAppOf ``cast && transport.isAppOf ``congrArg do throwError "expected a width-directed state cast"
  let stateEquality := mkAppN transport.getAppFn (transport.getAppArgs.pop.push toActive)
  let selectedState := mkAppN oldState.getAppFn #[fromState,toState,stateEquality,datum]
  return .letE partName partType selectedParts (.letE stateName stateType selectedState selectedGate stateUnused) partUnused

open Lean Elab Tactic in
local elab "paidOfferRead " observed:term:max : tactic => withMainContext do
  let receipt ← Term.elabTerm observed none
  let goal ← getMainGoal
  goal.assign (← instantiateMVars receipt)
  replaceMainGoal []

/-- The real offered state uses the indexed corrected page and the very
same middle-width identification as the signed-then-spill composition. -/
theorem selected_signed_target_bits (join : (paidOfferWidth% offerWidth)=layoutDomain cellChart)
    (z : State (layoutDomain cellChart) s) :
    selectedOfferStatement% (selectedOfferEvidence z) (afterParts) join := by
  paidOfferRead (selectedOfferEvidence z)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
