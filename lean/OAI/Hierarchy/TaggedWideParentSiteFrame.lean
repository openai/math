import OAI.Hierarchy.TaggedWideInstalledKeep
import OAI.Hierarchy.TaggedWideInstalledPrivate
import OAI.Hierarchy.TaggedWideInstalledPlane
import OAI.Hierarchy.TaggedWideWindowMask
import OAI.Hierarchy.TaggedWideWindowFullLocal

namespace OAI
/-! # One common physically mounted frame for the purchased windows and calendar cells -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.ParentFullCPUs
open ThreeFlat Routing
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PhysicalTerm
open HistoryRoles ReportSockets Tagged TaggedPrune TaggedShorterBudget ProtocolRAMFrozenWindow
open TaggedShorterSupergroups WideStack WideCalendarSites WideControlJoin WireTelescope Filter
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ} {v : FixedProtocolFormat F k p q Q σ Λ}
    {x : WideParent κ A} {m ell short : ℕ} {u : ℝ→ℝ} {δ ξ : ℝ} {unitCost N : ℕ}
    (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
local notation "G" => v.wideFullGates x m ell short u δ ξ unitCost cpu.room
local notation "cap" => v.wideInstalledCap unitCost
local notation "paid" => v.widePrivateUnit unitCost
local notation "histUnit" => v.wideHistoryUnit unitCost

structure SiteRoom : Prop where
  positive : WideParent.columnBits (cap*x.w)≤G.2.W+1
  privateBits : WideParent.columnBits (paid*x.w)≤G.2.W+1
  history : WideParent.columnBits (histUnit*x.w)≤G.2.W+1
  purchase : purchaseWordHeight v.W k v.wideJobs ell≤x.h

theorem cofinal_site_room : ∀ᶠx : WideParent κ A in WideParent.large κ A,
    ∀N (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x),cpu.SiteRoom := by
  have ht : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  filter_upwards [WideParent.columnBits_wordBits (κ:=κ) (A:=A) cap,
    WideParent.columnBits_wordBits (κ:=κ) (A:=A) paid,WideParent.columnBits_wordBits (κ:=κ) (A:=A) histUnit,
    ht.eventually (eventually_ge_atTop (purchaseWordHeight v.W k v.wideJobs ell))] with x a b c tall
  intro N cpu
  exact ⟨(a (2^v.W) copies).trans (Nat.le_succ _),(b (2^v.W) copies).trans (Nat.le_succ _),
    (c (2^v.W) copies).trans (Nat.le_succ _),tall⟩

local notation "days" => events v.mesh
local notation "d" => 2^v.W
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "rom" => v.wideInstalledRoot x
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
local notation "R" => CatalystArchive.fuel v.mesh*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) x.w
local notation "Private" => (v.widePlacement x.h x.w).catalogue.Private (v.wideOrder x.h x.w)
local notation "Data" => v.parentShared x m ell short unitCost ((days).length+1)
variable (ok : cpu.SiteRoom)
  (Z : CalendarTerms F x.h d k x.w R v.radius 1 slot days (v.wideOrigin x.h x.w size seed))
local notation "rout" => Z.nativeRouting Data
local notation "E" => OpenPins x.h x.w (rout).catalyst
local notation "Se" => Fin (rout).selectors
local notation "V" => SitePins E Se Data G.2
local notation "sites" => Fin (siteLast x.h d k+1)
local notation "endRoom" => v.wide_full_end x m ell short u δ ξ unitCost cpu.room
local notation "addr" => v.wideWindowWidthRow x m ell short u δ ξ cap dated v.maxBits rom G.2 endRoom
local notation "pWord" => Leaf.positiveWidthPin («E»:=E) («Se»:=Se) (Dst:=Data) G.2 (cap*x.w) addr ok.positive

def positiveGate : Net F V := Leaf.positiveMask (F:=F) (w:=x.w) (Fin.val : Fin (m+1)→ℕ) pWord
  (fun t q=>.inr (.inr (.inl (.inl ⟨t,q.1,q.2⟩))))

local notation "keep" => v.wideKeepNetwork x m ell short u δ ξ unitCost cpu.room E Se Data
local notation "pad" => cpu.positiveGate ok Z
local notation "priv" => v.widePrivateGate (Ex:=E) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room ok.privateBits
local notation "plane" => v.widePlane (Ex:=E) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room
local notation "timeline" => v.wideHistoryGate (Ex:=E) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room ok.history

/-- The only remaining site factors are the signed entry, last routed matrix
and actual transitions. The two programs, observations, five ordinary gates,
output wiring and both purchased oracle sockets are already fixed here. -/
def siteFrame (enter finish : sites→Net F V) (row : sites→Fin (days).length→Net F V) :=
  v.wideWindowLocalProgramsAt (u:=u) (δ:=δ) (ξ:=ξ) x m ell short v.maxBits cap dated rom Z
    (fun _:Private=>paid*x.w) roles ((days).length+1) (histUnit*x.w) G.1 G.2
    (cpu.firstPins (rout).catalyst) (cpu.paidPins (rout).catalyst) (0 : Fin 1) keep pad priv plane timeline enter finish row
    endRoom le_rfl ok.purchase

theorem siteFrame_installed (enter finish:sites→Net F V) (row : sites→Fin (days).length→Net F V) :
    (cpu.siteFrame ok Z enter finish row).frame.first=cpu.first.gate ∧
    (cpu.siteFrame ok Z enter finish row).frame.paid=cpu.paid.gate :=
  ⟨congrArg Prod.fst cpu.same,congrArg Prod.snd cpu.same⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.ParentFullCPUs

end
end OAI
