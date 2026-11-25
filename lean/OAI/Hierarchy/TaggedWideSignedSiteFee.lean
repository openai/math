import OAI.Hierarchy.TaggedWideFundedHardware
import OAI.Hierarchy.TaggedWideParentSiteFee
import OAI.Hierarchy.TaggedWideOriginalEntryPrice
import OAI.Hierarchy.TaggedWideTerminalSiteTariff

namespace OAI
/-! # The three original signed site tariffs and the complete installed site fee -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ThreeFlat Routing
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PhysicalTerm
open HistoryRoles ReportSockets Tagged TaggedPrune TaggedShorterBudget TaggedShorterSupergroups
open WideStack WideCalendarSites WideControlJoin WireTelescope Filter Real
open RoleProgram
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

def datedWork := ∑i,∑j,((a.step i j).cells+(a.step i j).internal)

/-- The two endpoint programs occupy the same site-pin type as the paid window
frame. Each uses the actual embedding and operand rows chosen by the calendar. -/
structure EndpointWiring (terminalWidth : ℕ) where
  history : Fin (((days).length+1)*Fintype.card ((r:R)×Fin (roles r))) ↪ D
  external : RoutingPin x.h x.w (fun _:Fin k=>Fintype.card (Columns x.h d)*res)→E
  base : ℕ
  operand : sites→TurnShelf.Aperture (TurnShelf.exponent v.wideShelfRoles) (TurnShelf.exponent (terminalWidth*x.w))→D⊕Bool
  first : ∀i,a.enter i=EntryOrder.firstNetwork («Se»:=Se) v.sampler roles days (G).2 history external F i
  last : ∀i,a.finish i=(G).2.shelfNet (F:=F) («E»:=E) (Q:=Se) («slots»:=slots) base i (operand i)

theorem installed_work (bounds : cpu.SiteRoom) :
    (a.installed bounds).frame.site.cells+(a.installed bounds).frame.site.internal=
      cpu.ordinaryWork bounds a.schedule+(∑i,((a.enter i).cells+(a.enter i).internal))+
      (∑i,((a.finish i).cells+(a.finish i).internal))+a.datedWork := by
  have bill:=cpu.frame_site_charge bounds a.schedule a.enter a.finish a.step (n:=0) (fun i=>Fin.elim0 i)
  change (a.installed bounds).frame.site.cells+(a.installed bounds).frame.site.internal=_ at bill
  simp only [Finset.sum_add_distrib] at bill
  unfold datedWork
  simp only [Finset.sum_add_distrib]
  omega

/-- The fixed endpoint coefficients absorb the entry, shelf and ordinary gates
at the larger of the genuine dated power and the single-log shelf power. -/
theorem price_of_dates (terminalWidth : ℕ) (positive : 0<terminalWidth)
    (C b : ℝ) (cpos : 0≤ C) :
    ∃K:ℝ,0≤ K ∧ ∀ᶠ x : WideParent κ A in WideParent.large κ A,
    ∀N (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (bounds : cpu.SiteRoom)
      (a : SignedSites v m ell short δ ξ unitCost cpu), a.EndpointWiring terminalWidth →
      (a.datedWork:ℝ)≤ C*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^b) →
      (((a.installed bounds).frame.site.cells+(a.installed bounds).frame.site.internal:ℕ):ℝ)≤
        K*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^(max 1 b)) := by
  obtain ⟨O,hO,ordinary⟩:=ParentFullCPUs.cofinal_ordinary_fee (v:=v) (κ:=κ) (A:=A) (m:=m) (ell:=ell)
    (short:=short) (u:=u) (δ:=δ) (ξ:=ξ) (unitCost:=unitCost)
  obtain ⟨T,hT,terminal⟩:=v.wide_terminal_site_price (κ:=κ) (A:=A) terminalWidth positive
  refine ⟨O+v.wideExteriorFactor+T+C,by positivity,?_⟩
  have high : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  filter_upwards [ordinary,terminal,high.eventually ((tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop («R»:=ℝ))).eventually_ge_atTop 1)] with x ord shelf high
  intro N cpu bounds a endpoints datesBound
  let gate:=(v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
  let historyCap:=HistoryRoles.ceiling v.sampler (h:=x.h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
    v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) x.w
  let shared:=v.parentShared x m ell short unitCost ((events v.mesh).length+1)
  let selectors:=Fin (a.schedule.nativeRouting shared).selectors
  let vol:=(2:ℝ)^x.h*x.w
  let L:=log (x.h:ℝ)
  change 1≤ L at high
  have hvol : 0≤ vol:=by positivity
  have base : 1≤ L^(max 1 b):=Real.one_le_rpow high (zero_le_one.trans (le_max_left ..))
  have one : L≤ L^(max 1 b):=by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le high (le_max_left 1 b)
  have rise : L^b≤ L^(max 1 b):=Real.rpow_le_rpow_of_exponent_le high (le_max_right ..)
  have first : ((∑i,((a.enter i).cells+(a.enter i).internal):ℕ):ℝ)≤ (v.wideExteriorFactor:ℝ)*vol := by
    simp_rw [endpoints.first]
    simpa only [vol,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      (Nat.cast_le (α:=ℝ)).mpr (v.wide_entry_price x.h x.w (events v.mesh) gate historyCap endpoints.history endpoints.external
        («Se»:=selectors) x.property.1.2.1)
  have last : ((∑i,((a.finish i).cells+(a.finish i).internal):ℕ):ℝ)≤ T*(vol*L) := by
    simp_rw [endpoints.last]
    exact shelf gate endpoints.base endpoints.operand
  have widen (Z : ℝ) (nonneg : 0≤ Z) {a c : ℝ} (small : a≤ c) : Z*(vol*a)≤ Z*(vol*c) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left small hvol) nonneg
  have first' : ((∑i,((a.enter i).cells+(a.enter i).internal):ℕ):ℝ)≤ v.wideExteriorFactor*(vol*L^(max 1 b)) :=
    first.trans (by simpa only [mul_one] using widen v.wideExteriorFactor (by positivity) base)
  have last':=last.trans (widen T hT.le one)
  have ord':=(ord N cpu bounds a.schedule).trans (widen O hO one)
  have step':=datesBound.trans (widen C cpos rise)
  rw [a.installed_work bounds]
  simp only [Nat.cast_add]
  change _≤ (O+v.wideExteriorFactor+T+C)*(vol*L^(max 1 b))
  simp only [add_mul]
  linarith only [ord',first',last',step']

end SignedSites
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
