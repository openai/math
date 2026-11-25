import OAI.Hierarchy.TaggedWideCalendarEndpointDay
import OAI.Hierarchy.TaggedWideCalendarEndpointFinish
import OAI.Hierarchy.TaggedWideCalendarPartyWords
import OAI.Hierarchy.TaggedWideCalendarHistoryRead
import OAI.Hierarchy.TaggedWideCalendarControlRoom
import OAI.Hierarchy.TaggedWireActualRoutedSchedule
import OAI.Hierarchy.TaggedWideSelectedFirstNetwork
import OAI.Hierarchy.TaggedWideFixedProtocol
import OAI.Hierarchy.TaggedWideNativeFamily

namespace OAI
/-! # Width reduction from the two native programs and the funded calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage CoreBoard Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Tagged WireTelescope CalendarTape CoreBoard.PhysicalTerm
open scoped Classical
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 240000
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size)
    (seed : Boot.Tape h (2^v.W)) (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h)
    (small : width ≤ 2^h) (expanse : v.wideFundedSize h width v.maxBits ≤ size)
    (late : v.rowScheduleHeight ≤ h) (floor : v.widthFloor ≤ width) (word : v.ReportWordRoom h width)
local notation "slots" => (v.wideSelector h width age budget small).format.slot
local notation "es" => events v.mesh
local notation "state" => v.wideOrigin h width size seed
local notation "tall" => (max_le_iff.mp late).1

private theorem assembledRowsFields
    (incoming : ∀(p : Equiv.Perm (Row h)) {a tail x} (t : WireTelescope.CalendarTape.Prefix slots es (state p) (.attempt a::tail) x),
      v.sourceRows h width size extent p seed age budget small t tall floor)
    (outgoing : ∀(p : Equiv.Perm (Row h)) {a tail x} (t : WireTelescope.CalendarTape.Prefix slots es (state p) (.attempt a::tail) x),
      v.targetRows h width size extent p seed age budget small t tall floor)
    (reportAge : v.reportHeight ≤ h) :
    let stream := v.with_elected_rows h width size extent seed age budget small expanse late floor word incoming outgoing
    (∀ p, WireTelescope.CalendarTape.Prefix.atWidth (stream.width p) =
      WireTelescope.CalendarTape.Prefix.atWidth (v.wideCursorWidth h width size p seed age budget small)) ∧
      ∀ p j, reportGeometry p (stream.reported p j) =
        reportGeometry p (v.wide_reported_path h width size p seed age budget small expanse reportAge word j) := by
  exact ⟨fun _ => rfl, fun _ _ => rfl⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A s ε δ η ξ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m short : ℕ) (u : ℝ→ℝ)
local notation "ell" => v.calendarLaneExponent
local notation "unit" => v.calendarUnit
local notation "geom" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geom).menu u δ ξ
variable {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x)
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unit
local notation "S" => v.wideInstalledSize x m ell unit g
local notation "funded" => (v.wide_installed_tape_bounds x m ell unit g).2.2
local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans funded
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unit g
  (v.wide_dated_sites h width ell unit) (v.wide_dated_edges h width ell unit) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "head" => v.wideOrigin h width S seed
local notation "report" p:arg j:arg => v.wide_reported_path h width S p seed cpu.age cpu.ready.credit cpu.ready.size_le
  funded support.size.late support.size.words j

/-- Chronology with the genuine emitted terminal geometry, fixed for all
external bits and paid purchases of this particular installed parent. -/
private structure CalendarAgreement (Plan : Type) (WidthLaw ReportLaw : Plan → Prop) where
  dates : Plan
  widths : WidthLaw dates
  reported : ReportLaw dates

local notation "chronologyPlan" => CalendarTerms F h d k width (fuel v.mesh*width) v.radius 1 sl es head
local notation "calendarWidths" => fun plan : chronologyPlan => ∀ perm, CalendarTape.Prefix.atWidth (plan.width perm) =
  CalendarTape.Prefix.atWidth (v.wideCursorWidth h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le)
local notation "calendarReports" => fun plan : chronologyPlan => ∀ perm path, reportGeometry perm (plan.reported perm path) =
  reportGeometry perm (report perm path)
abbrev CompilerCalendar := CalendarAgreement chronologyPlan calendarWidths calendarReports

namespace CompilerCalendar
variable {v m short u x cpu support}
variable (calendar : v.CompilerCalendar m short u x cpu support)
abbrev dates := CalendarAgreement.dates calendar
abbrev widths := CalendarAgreement.widths calendar
abbrev reported := CalendarAgreement.reported calendar
abbrev mk := @CalendarAgreement.mk chronologyPlan calendarWidths calendarReports
abbrev rec := @CalendarAgreement.rec chronologyPlan calendarWidths calendarReports
abbrev casesOn := @CalendarAgreement.casesOn chronologyPlan calendarWidths calendarReports
end CompilerCalendar

variable (late : v.rowScheduleHeight≤h)
local notation "tall" => (max_le_iff.mp late).1
local notation "floor" => support.size.widthFloor

/-- The finite chronological construction discharges the terminal geometry
field by reduction on its original complete path. -/
def compilerCalendarOfRows
    (incoming : ∀(p : Equiv.Perm (Tagged.Row h)) {a tail state} (t : CalendarTape.Prefix sl es (head p) (.attempt a::tail) state),
      v.sourceRows h width S extent p seed cpu.age cpu.ready.credit cpu.ready.size_le t tall floor)
    (outgoing : ∀(p : Equiv.Perm (Tagged.Row h)) {a tail state} (t : CalendarTape.Prefix sl es (head p) (.attempt a::tail) state),
      v.targetRows h width S extent p seed cpu.age cpu.ready.credit cpu.ready.size_le t tall floor) :
    v.CompilerCalendar m short u x cpu support where
  dates:=v.with_elected_rows h width S extent seed cpu.age cpu.ready.credit cpu.ready.size_le
    funded late floor support.size.words incoming outgoing
  widths := (assembledRowsFields v h width S extent seed cpu.age cpu.ready.credit cpu.ready.size_le
    funded late floor support.size.words incoming outgoing support.size.late).1
  reported := (assembledRowsFields v h width S extent seed cpu.age cpu.ready.credit cpu.ready.size_le
    funded late floor support.size.words incoming outgoing support.size.late).2

/-- Native election, original incidences and terminal geometry for every
physical history of a given parent. -/
def compilerCalendar (routeAge : v.routingHeight≤h) : v.CompilerCalendar m short u x cpu support where
  dates:=v.routedSchedule h width S extent seed cpu.age cpu.ready.credit cpu.ready.size_le
    funded routeAge floor support.size.words
  widths:=fun _=>rfl
  reported:=fun _ _=>rfl

variable {C : ℝ} (prices : v.PhysicalCounts u A δ ξ m) (hκ : 0<κ)
local notation "group" => GroupRoom v.W k v.wideJobs u δ ξ menu x
local notation "metadataFits" => ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x

/-- Site equations on the chosen paid return. All free inputs are physical
source rows or endpoint bit evaluations on the actual two-program trace. -/
def CalendarSitesRead (room : cpu.SiteRoom) (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (D : v.CompilerCalendar m short u x cpu support) (groups : group) (metadata : metadataFits) : Prop :=
  ∀items ext p rank tag,v.wideCalendarEndpointReads (C:=C) m ell short u δ ξ x cpu room control support
    D.dates D.reported prices hκ.le groups metadata v.calendar_lanes items ext p rank tag

attribute [local irreducible] wideCalendarEndpointField wideCalendarEndpointReads

private theorem paidSiteNetworks (room : cpu.SiteRoom) (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (D : v.CompilerCalendar m short u x cpu support) (groups : group) (metadata : metadataFits)
    (height : v.BranchRoleHeight h width)
    (reads : ∀items ext p rank tag,
      let field:=v.wideCalendarEndpointField (C:=C) m ell short u δ ξ x cpu room control support
        D.dates D.reported prices hκ.le groups metadata v.calendar_lanes items ext p rank tag height D.widths
      field .historyMask ∧ field .first ∧ field .finish ∧ field .steps) :
    v.CalendarSitesRead (C:=C) m short u x cpu support prices hκ room control D groups metadata := by
  intro items ext permutation rank tag
  have observations := reads items ext permutation rank tag
  exact v.wide_calendar_endpoint_reads (C:=C) m ell short u δ ξ x cpu room control support
    D.dates D.reported prices hκ.le groups metadata v.calendar_lanes items ext permutation rank tag height D.widths
    observations.1 observations.2.1 observations.2.2.1 observations.2.2.2

/-- All paths use the same physical placement for the first, last and
per-date rows. The history-mask component is the authenticated native width
table at the actual selected return. -/
theorem CalendarSitesRead.of_three (room : cpu.SiteRoom) (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (D : v.CompilerCalendar m short u x cpu support) (groups : group) (metadata : metadataFits)
    (height : v.BranchRoleHeight h width)
    (word : WideParent.columnBits (v.wideHistoryUnit unit*width)≤Native.wordBits h d Native.copies)
    (reads : ∀items ext p rank tag,
      let field:=v.wideCalendarEndpointField (C:=C) m ell short u δ ξ x cpu room control support
        D.dates D.reported prices hκ.le groups metadata v.calendar_lanes items ext p rank tag height D.widths
      field .first ∧ field .finish ∧ field .steps) :
    v.CalendarSitesRead (C:=C) m short u x cpu support prices hκ room control D groups metadata := by
  apply paidSiteNetworks v m short u x cpu support prices hκ room control D groups metadata height
  intro items ext perm rank tag
  exact ⟨v.wide_calendar_history_mask (C:=C) m ell short u δ ξ x cpu room control support
    D.dates D.reported prices hκ.le groups metadata v.calendar_lanes items ext perm rank tag height D.widths word,
    reads items ext perm rank tag⟩

local notation "schedule" r:arg => v.compilerCalendar m short u x cpu support r

/-- The funded initial condition, dated occupancy, and the terminal report
on the actual paid heap share the same selected chronological placement. -/
theorem routed_calendar_read (room : cpu.SiteRoom) (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (groups : group) (metadata : metadataFits) (height : v.BranchRoleHeight h width) (routeAge : v.routingHeight≤h)
    (terminal : v.CalendarTerminalRoom x)
    (word : WideParent.columnBits (v.wideHistoryUnit unit*width)≤Native.wordBits h d Native.copies)
    (reads : ∀items ext p rank tag,
      let D:=schedule routeAge
      let field:=v.wideCalendarEndpointField (C:=C) m ell short u δ ξ x cpu room control support
        D.dates D.reported prices hκ.le groups metadata v.calendar_lanes items ext p rank tag height D.widths
      field .steps) :
    v.CalendarSitesRead (C:=C) m short u x cpu support prices hκ room control (schedule routeAge) groups metadata := by
  apply CalendarSitesRead.of_three v m short u x cpu support prices hκ room control (schedule routeAge)
    groups metadata height word
  intro items ext p rank tag
  have done:=v.calendar_endpoint_finish (C:=C) m ell short u δ ξ x cpu room control support routeAge
    prices hκ.le groups metadata v.calendar_lanes items ext p rank tag height terminal
  have steps:=reads items ext p rank tag
  have limits:=max_le_iff.mp routeAge
  have levels:=max_le_iff.mp limits.1
  have ages:=limits.1
  simp only [rowScheduleHeight,max_le_iff] at ages
  have cap:v.wideFundedHeight≤h:=ages.2.2.2.2.2.2
  refine ⟨?_,done,steps⟩
  exact v.wideCalendar_first_field (C:=C) m ell short u δ ξ x cpu room control support limits.1
    (fun p {_ _ _} t => v.funded_source_rows h width S extent p seed cpu.age cpu.ready.credit cpu.ready.size_le
      t levels.1 floor funded cap)
    (fun p {_ _ _} t => v.funded_target_rows h width S extent p seed cpu.age cpu.ready.credit cpu.ready.size_le
      t levels.1 floor (max_le_iff.mp limits.2).1 (max_le_iff.mp limits.2).2)
    prices hκ.le groups metadata v.calendar_lanes items ext p rank tag height

/-- The lane exponent, calendar tensors, RAM programs and accounting
constants are fixed before purchasing the two compactors. -/
def PricedCalendarInputs (pricePos : 0<κ) : Prop :=
  ∀m:ℕ,∀prices:v.PhysicalCounts u A δ ξ m,∀short:ℕ,∀C:ℝ,0≤C→∀ᶠ x : WideParent κ A in WideParent.large κ A,
    ∀(routeAge : v.routingHeight≤x.h)(height : v.BranchRoleHeight x.h x.w),v.PartyWordBounds x.h x.w unit → v.CalendarTerminalRoom x →
    ∀N (cpu:v.ParentFullCPUs m ell short u δ ξ unit N x) (room:cpu.SiteRoom)
      (control:SignedSites.CalendarControlRoom (cpu:=cpu))
      (support:v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x),
    ∀groups:GroupRoom v.W k v.wideJobs u δ ξ
      ((typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ) x,
    ∀metadata:(∀t:Fin (m+1),
      let M:=(typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
      1+M.height t x+M.height t x≤M.payload t x),
      ∀items ext p rank tag date,v.calendarDayRead (C:=C) m ell short u δ ξ x cpu room control support
        routeAge prices pricePos.le groups metadata v.calendar_lanes items ext p rank tag height date

private theorem paidConditionsTogether {X : Type*} {f : Filter X} {P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : X → Prop}
    (p1 : ∀ᶠ x in f, P1 x)
    (p2 : ∀ᶠ x in f, P2 x)
    (p3 : ∀ᶠ x in f, P3 x)
    (p4 : ∀ᶠ x in f, P4 x)
    (p5 : ∀ᶠ x in f, P5 x)
    (p6 : ∀ᶠ x in f, P6 x)
    (p7 : ∀ᶠ x in f, P7 x)
    (p8 : ∀ᶠ x in f, P8 x)
    (p9 : ∀ᶠ x in f, P9 x)
    (p10 : ∀ᶠ x in f, P10 x) : ∀ᶠ x in f, P1 x ∧ P2 x ∧ P3 x ∧ P4 x ∧ P5 x ∧ P6 x ∧ P7 x ∧ P8 x ∧ P9 x ∧ P10 x :=
  p1.and (p2.and (p3.and (p4.and (p5.and (p6.and (p7.and (p8.and (p9.and (p10)))))))))


section
variable (admissible : TaggedWidthProfile.Admissible s u) (positive : 0 < κ) (large : 1 < A)
variable (C : ℝ) (paid : 0 ≤ C)
variable (groups : ∀ᶠ x in WideParent.large κ A, GroupRoom v.W k v.wideJobs u δ ξ menu x)
variable (requirements : v.PricedCalendarInputs (A:=A) (δ:=δ) (ξ:=ξ) u positive)
private abbrev paidCalendarConditions :=
  let installed := SignedSites.cofinal_priced_calendar (κ:=κ) (A:=A) (u:=u) (δ:=δ) (ξ:=ξ)
    v m ell short unit v.calendarTerminalWidth v.calendarTerminalWidth_pos
  let family := typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
  let heights : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop := tendsto_comap
  paidConditionsTogether installed.choose_spec.2
    (v.cofinal_selected_return_support (κ:=κ) (A:=A) m ell short u δ ξ unit admissible v.calendarUnit_rate)
    groups (family.metadata (δ:=δ) (ξ:=ξ) u positive large)
    (heights.eventually (eventually_ge_atTop v.routingHeight))
    (v.cofinal_BranchRoleHeight (κ:=κ) (A:=A))
    (WideParent.columnBits_wordBits (κ:=κ) (A:=A) (v.wideHistoryUnit unit))
    (v.cofinal_party_word (κ:=κ) (A:=A) unit)
    (v.cofinal_calendar_terminal_room (κ:=κ) (A:=A))
    (requirements m prices short C paid)

end

private def PaidSiteEvaluation (pricePos : 0<κ) : Prop :=
  ∀m:ℕ,∀prices:v.PhysicalCounts u A δ ξ m,∀short:ℕ,∀C:ℝ,∀x : WideParent κ A,
    ∀(routeAge : v.routingHeight≤x.h)(height : v.BranchRoleHeight x.h x.w),WideParent.columnBits (v.wideHistoryUnit unit*x.w) ≤ Native.wordBits x.h (2^v.W) Native.copies → v.PartyWordBounds x.h x.w unit → v.CalendarTerminalRoom x →
    ∀N (cpu:v.ParentFullCPUs m ell short u δ ξ unit N x) (room:cpu.SiteRoom)
      (control:SignedSites.CalendarControlRoom (cpu:=cpu))
      (support:v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x),
    ∀groups:GroupRoom v.W k v.wideJobs u δ ξ
      ((typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ) x,
    ∀metadata:(∀t:Fin (m+1),
      let M:=(typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
      1+M.height t x+M.height t x≤M.payload t x),
      (∀items ext p rank tag date,v.calendarDayRead (C:=C) m ell short u δ ξ x cpu room control support
        routeAge prices pricePos.le groups metadata v.calendar_lanes items ext p rank tag height date) →
      let plan := v.compilerCalendar m short u x cpu support routeAge
      (SignedSites.ofCalendar (cpu:=cpu) plan.dates control v.calendarTerminalWidth
        (v.calendarTerminalPins x m ell short)).Evaluates room C

private theorem compilerFromDailySites (hu : TaggedWidthProfile.Admissible s u) (positive : 0<κ) (large : 1<A)
    (evaluation : PaidSiteEvaluation (A:=A) (δ:=δ) (ξ:=ξ) v u positive)
    (price : Choice u A ε p q Q σ Λ δ η ξ) (fields : v.PricedCalendarInputs (A:=A) (δ:=δ) (ξ:=ξ) u positive) :
    v.Compiler (κ:=κ) u price := by
  intro m prices
  refine ⟨v.calendarLaneExponent,?_⟩
  intro short C paid groups
  let paidHardware := SignedSites.cofinal_priced_calendar
    (κ:=κ) (A:=A) (u:=u) (δ:=δ) (ξ:=ξ) v m v.calendarLaneExponent short v.calendarUnit
    v.calendarTerminalWidth v.calendarTerminalWidth_pos
  let rate := paidHardware.choose
  have nonnegative : 0 ≤ rate := paidHardware.choose_spec.1
  apply v.hardware_of_signed_sites m v.calendarLaneExponent short δ ξ v.calendarUnit hu C rate 3
    nonnegative (by norm_num)
  apply Filter.Eventually.mono (paidCalendarConditions (v:=v) (u:=u) (s:=s) (m:=m) (short:=short)
    (prices:=prices) (admissible:=hu) (positive:=positive) (large:=large) (C:=C) (paid:=paid)
    (groups:=groups) (requirements:=fields))
  intro x completed
  rcases completed with ⟨bill,support,groupsFit,widths,routeAge,roleHeight,memoryRoom,partyWord,terminalWord,exhibits⟩
  intro N cpu room
  obtain ⟨reads,tally⟩:=bill N cpu
  let D:=v.compilerCalendar m short u x cpu support routeAge
  refine ⟨SignedSites.ofCalendar (cpu:=cpu) D.dates reads v.calendarTerminalWidth
    (v.calendarTerminalPins x m ell short), ?_, ?_⟩
  · exact evaluation m prices short C x routeAge roleHeight (memoryRoom (2^v.W) Native.copies)
      partyWord terminalWord N cpu room reads support groupsFit widths
      (exhibits routeAge roleHeight partyWord terminalWord N cpu room reads support groupsFit widths)
  · exact tally room D.dates (v.calendarTerminalPins x m ell short)

theorem calendar_compiler (hu : TaggedWidthProfile.Admissible s u) (positive : 0<κ) (large : 1<A)
    (price : Choice u A ε p q Q σ Λ δ η ξ) (fields : v.PricedCalendarInputs (A:=A) (δ:=δ) (ξ:=ξ) u positive) :
    v.Compiler (κ:=κ) u price := by
  apply compilerFromDailySites (v:=v) (u:=u) hu positive large _ price fields
  intro m prices short C x routeAge height memoryRoom partyWord terminal N cpu room control support groupsFit widths allDates
  let D := v.compilerCalendar m short u x cpu support routeAge
  have endpoints := v.routed_calendar_read (C:=C) m short u x cpu support prices positive room control
    groupsFit widths height routeAge terminal memoryRoom
    (fun items ext perm rank tag => v.calendar_steps_of_dates (C:=C) m ell short u δ ξ x cpu room control support
      routeAge prices positive.le groupsFit widths v.calendar_lanes items ext perm rank tag height
      (allDates items ext perm rank tag))
  exact v.wide_calendar_evaluates (C:=C) m ell short u δ ξ x cpu room control support
    D.dates D.reported prices positive.le groupsFit widths v.calendar_lanes endpoints

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
namespace Hierarchy.Tagged
set_option maxHeartbeats 1200000
open ProtocolRAM.Calendar TaggedShorterBudget

/-- The protocol quantifiers follow from the actual physical compiler for
the selected sampler and signed format. -/
def calendar_readouts {F : Type} [Field F] {k : ℕ} (hk:0<k) (missing:¬HasSpectralFlat F (k+1))
    (charts : ∀{u : ℝ→ℝ}{κ A ε p q Q σ Λ δ η ξ : ℝ},TaggedWidthProfile.Admissible (profile F k 1) u→
      ∀hκ:0<κ,1+κ≤A→0<ε→∀v:FixedProtocolFormat F k p q Q σ Λ,
        Choice u A (ε/2) p q Q σ Λ δ η ξ→v.PricedCalendarInputs (A:=A) (δ:=δ) (ξ:=ξ) u hκ) : CofinalReadouts F k :=
by
  apply fixed_readouts hk missing
  intro u κ A ε p q Q σ Λ δ η ξ hu hκ hA hε v price
  have large : 1 < A := by linarith only [hA, hκ]
  have paid : v.PricedCalendarInputs (A:=A) (δ:=δ) (ξ:=ξ) u hκ :=
    @charts u κ A ε p q Q σ Λ δ η ξ hu hκ hA hε v price
  exact v.native_readout hu hκ.le price (v.calendar_compiler u hu hκ large price paid)

theorem calendar_reductions {F : Type} [Field F] {k : ℕ} (hk:0<k) (missing:¬HasSpectralFlat F (k+1))
    (charts : ∀{u : ℝ→ℝ}{κ A ε p q Q σ Λ δ η ξ : ℝ},TaggedWidthProfile.Admissible (profile F k 1) u→
      ∀hκ:0<κ,1+κ≤A→0<ε→∀v:FixedProtocolFormat F k p q Q σ Λ,
        Choice u A (ε/2) p q Q σ Λ δ η ξ→v.PricedCalendarInputs (A:=A) (δ:=δ) (ξ:=ξ) u hκ) :
    WidthReductions F k :=
  let r:=calendar_readouts hk missing charts
  widthReductions_of_protocol hk r.protocols r.readout

end Hierarchy.Tagged
end

end OAI
