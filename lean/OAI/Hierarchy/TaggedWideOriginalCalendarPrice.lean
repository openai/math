import OAI.Hierarchy.TaggedWideSignedDatedPrice
import OAI.Hierarchy.ProbeFixedWideCalendarRow

namespace OAI
/-! # Price on the installed parent calendar at its original public addresses -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ThreeFlat Routing
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PhysicalTerm
open HistoryRoles ReportSockets Tagged TaggedPrune TaggedShorterBudget TaggedShorterSupergroups
open WideStack WideCalendarSites WideControlJoin WireTelescope Filter Real
open RoleProgram WireTelescope.PassMatrix WideCPU
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A s : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) {u : ℝ→ℝ}
    (δ ξ : ℝ) (unitCost : ℕ) {N : ℕ} {x : WideParent κ A}
variable (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
local notation "days" => events v.mesh
local notation "d" => 2^v.W
local notation "g" => v.wideDated x.h x.w ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
local notation "G" => v.wideFullGates x m ell short u δ ξ unitCost cpu.room
local notation "D" => v.parentShared x m ell short unitCost ((days).length+1)
local notation "sites" => Fin (siteLast x.h d k+1)

namespace SignedSites
variable {v m ell short δ ξ unitCost cpu}
variable (a : SignedSites v m ell short δ ξ unitCost cpu)
local notation "rout" => a.schedule.nativeRouting D
local notation "E" => OpenPins x.h x.w (rout).catalyst
local notation "Se" => Fin (rout).selectors
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) x.w
local notation "res" => CatalystArchive.fuel v.mesh*x.w
local notation "R" => Public v.sampler x.h v.W k v.wideJobs
local notation "slots" => WordSeats.room (k:=k) (attempts:=v.wideJobs) v.sampler


local notation "rom" => v.wideInstalledRoot x
local notation "layout" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (layout).pruneScratch+(layout).pruneRows+1
local notation "Time" => Fin (((days).length+1)*Fintype.card ((r:R)×Fin (roles r)))

/-- The chronological input of the native row is the actual time component
of the numbered four-block parent workspace. -/
def calendarTime (i : Time) : D := .inr (.inr (.inl i))

/-- The numbered parent history embedding is definitionally the time bank of
the reindexed workspace used by the original first-network theorem. -/
def calendarHistory : Time ↪ D := EntryOrder.timePin («D»:=D) (Equiv.refl _)

local notation "spill" => v.wideSpillDates x.h x.w ell unitCost v.maxBits first
local notation "rank" => v.wideSpillRankEnd x.h x.w v.maxBits first
local notation "ctrl" => (spill).spillControlWork rank
local notation "sign" => (spill).roleRoot rank 2
local notation "shelf" => (v.wideTurnWindow x.h x.w v.maxBits ((g).workEnd S)).base
local notation "hist" => calendarHistory (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unitCost)
local notation "terminalPins" K => sites→TurnShelf.Aperture
  (TurnShelf.exponent v.wideShelfRoles) (TurnShelf.exponent (K*x.w))→D⊕Bool

/-- Address and word bounds for the two original control planes and their
literal ballot at every numbered site and date of the corrected calendar. -/
structure CalendarControlRoom : Prop where
  spillRead : ∀ s : sites,∀ j : Fin (days).length,∀ f : SiteControls.Field v.widePacketDegree,
    controlAddress g ctrl j s f<(G).2.u
  signedRead : ∀ s : sites,∀ j : Fin (days).length,∀ f : SiteControls.Field v.widePacketDegree,
    controlAddress g sign j s f<(G).2.u
  mode : ∀ s : sites,∀ j : Fin (days).length,ballotAddress g sign j s 0<(G).2.u
  tag : v.signedTagCeiling≤ (G).2.W+1
  lane : v.wideNeighborDigits x.w unitCost≤ (G).2.W+1

variable (Z : CalendarTerms F x.h d k x.w res v.radius 1 slot days (v.wideOrigin x.h x.w S seed))

/-- The three circuits of the real full CPU, using its fixed corrected-spill
addresses, original five-column terminal shelf and tagged routing ports. -/
def ofCalendar (reads : CalendarControlRoom (cpu:=cpu)) (terminalWidth : ℕ)
    (operand : terminalPins terminalWidth) : SignedSites v m ell short δ ξ unitCost cpu where
  schedule := Z
  enter := EntryOrder.firstNetwork («Se»:=Fin (Z.nativeRouting D).selectors) v.sampler roles days (G).2
    hist routingPort F
  finish := fun i=>(G).2.shelfNet (F:=F) («slots»:=slots) shelf i (operand i)
  step := fun i j=>v.calendarRow x.h x.w ell unitCost v.maxBits rom S ((g).romEnd rom)
    ((g).workEnd S) first (G).2 hist i j (reads.spillRead i j) (reads.signedRead i j) (reads.mode i j) reads.tag reads.lane

def ofCalendar_endpoints (reads : CalendarControlRoom (cpu:=cpu)) (terminalWidth : ℕ)
    (operand : terminalPins terminalWidth) : (ofCalendar Z reads terminalWidth operand).EndpointWiring terminalWidth :=
  ⟨hist,routingPort,shelf,operand,fun _=>rfl,fun _=>rfl⟩

/-- Every original signed transition is the native circuit at its genuine
paid date and vertex, after the corrected scatter terminates. The address
inequalities certify its reads in the observed completed RAM. -/
def CalendarRows : Prop := ∀i j,∃ control signedControl mode tagSmall laneSmall,
    a.step i j=v.calendarRow (Ex:=E) (Sel:=Se) (Data:=D) x.h x.w ell unitCost v.maxBits
      rom S ((g).romEnd rom) ((g).workEnd S) first (G).2
      (calendarTime (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unitCost))
      i j control signedControl mode tagSmall laneSmall

theorem ofCalendar_rows (reads : CalendarControlRoom (cpu:=cpu)) (terminalWidth : ℕ)
    (operand : terminalPins terminalWidth) : (ofCalendar Z reads terminalWidth operand).CalendarRows := by
  intro i j
  exact ⟨reads.spillRead i j,reads.signedRead i j,reads.mode i j,reads.tag,reads.lane,rfl⟩

/-- A single cubic logarithmic power pays for the actual signed stock rows,
physical endpoint comparators and all five ordinary gates. Only identification
of those circuits with the installed site triple is required. -/
theorem price_of_calendar_rows (terminalWidth : ℕ) (positive : 0<terminalWidth) :
    ∃C:ℝ,0≤ C ∧ ∀ᶠ x : WideParent κ A in WideParent.large κ A,
      ∀ N (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (bounds : cpu.SiteRoom)
        (a : SignedSites v m ell short δ ξ unitCost cpu),
      a.EndpointWiring terminalWidth → a.CalendarRows →
      (((a.installed bounds).frame.site.cells+(a.installed bounds).frame.site.internal:ℕ):ℝ)≤
        C*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^(3:ℝ)) := by
  obtain ⟨P,K,_,row⟩:=v.calendarRow_tariff unitCost
  obtain ⟨C,hC,fee⟩:=price_of_steps (v:=v) (κ:=κ) (A:=A) (m:=m) (ell:=ell)
    (short:=short) (u:=u) (δ:=δ) (ξ:=ξ) (unitCost:=unitCost) terminalWidth P K positive
  refine ⟨C,hC,?_⟩
  filter_upwards [fee] with x bound
  intro N cpu bounds a endpoints realRows
  apply bound N cpu bounds a endpoints
  intro i j
  obtain ⟨control,signedControl,mode,tagSmall,laneSmall,actual⟩:=realRows i j
  rw [actual]
  exact row x.h x.w ell v.maxBits _ _ _ _ _ x.formats.2.1 _ _ i j control signedControl mode tagSmall laneSmall

/-- The original parent assembly has a cofinal site tariff. The only public
inputs are the funded schedule, actual aperture wiring, and native read bounds. -/
theorem price_ofCalendar (terminalWidth : ℕ) (positive : 0<terminalWidth) :
    ∃C:ℝ,0≤ C ∧ ∀ᶠ x : WideParent κ A in WideParent.large κ A,
      ∀ N (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (bounds : cpu.SiteRoom)
        (Z : CalendarTerms F x.h (2^v.W) k x.w (CatalystArchive.fuel v.mesh*x.w) v.radius 1
          (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot (events v.mesh)
          (v.wideOrigin x.h x.w (v.wideInstalledSize x m ell unitCost (v.wideDated x.h x.w ell unitCost))
            (v.wideInstalledHeader x m ell short u δ ξ unitCost (v.wideDated x.h x.w ell unitCost)
              (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0))))
        (reads : CalendarControlRoom (cpu:=cpu)) operand,
      let a:=ofCalendar Z reads terminalWidth operand
      (((a.installed bounds).frame.site.cells+(a.installed bounds).frame.site.internal:ℕ):ℝ)≤
        C*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^(3:ℝ)) := by
  obtain ⟨C,pos,price⟩:=price_of_calendar_rows (v:=v) (κ:=κ) (A:=A) (m:=m) (ell:=ell)
    (short:=short) (u:=u) (δ:=δ) (ξ:=ξ) (unitCost:=unitCost) terminalWidth positive
  refine ⟨C,pos,?_⟩
  filter_upwards [price] with x paid
  intro N cpu bounds Z reads operand
  exact paid N cpu bounds _ (ofCalendar_endpoints Z reads terminalWidth operand) (ofCalendar_rows Z reads terminalWidth operand)

end SignedSites
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
