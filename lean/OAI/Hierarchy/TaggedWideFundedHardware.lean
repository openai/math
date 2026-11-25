import OAI.Hierarchy.TaggedWideParentSiteFrame

namespace OAI
/-! # Closing the public hardware quantifiers from the signed site executions -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ThreeFlat Routing
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PhysicalTerm
open HistoryRoles ReportSockets Tagged TaggedPrune TaggedShorterBudget TaggedShorterSupergroups
open WideStack WideCalendarSites WideControlJoin WireTelescope Filter Real
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A s : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) {u : ℝ→ℝ}
    (δ ξ : ℝ) (unitCost : ℕ) {N : ℕ} {x : WideParent κ A}
variable (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
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
local notation "V" Z:arg => SitePins (OpenPins x.h x.w ((Z).nativeRouting D).catalyst)
  (Fin ((Z).nativeRouting D).selectors) D (G).2

/-- The tensors of the actual funded trajectory, with their uniform public
entry, finish and transition circuits on the fixed finite full frame. -/
structure SignedSites where
  schedule : CalendarTerms F x.h d k x.w (CatalystArchive.fuel v.mesh*x.w) v.radius 1
    slot days (v.wideOrigin x.h x.w S seed)
  enter : sites→Net F (V schedule)
  finish : sites→Net F (V schedule)
  step : sites→Fin (days).length→Net F (V schedule)

variable {v m ell short δ ξ unitCost cpu}
namespace SignedSites
variable (a : SignedSites v m ell short δ ξ unitCost cpu) (bounds : cpu.SiteRoom)
def installed := cpu.siteFrame bounds a.schedule a.enter a.finish a.step
local notation "J" => a.installed bounds
local notation "menu" => v.wideWindowMenu m ell short u δ ξ
local notation "source" => fun _ : Fin (m+1)=>purchaseSlots x.h v.W k v.wideJobs ell
local notation "count" => purchaseModules v.W u δ ξ menu x
local notation "target" => fun i=>purchaseCandidates x.h v.W k v.wideJobs (source i) ((menu).height i x) (count i)
variable {C : ℝ} (items : PurchaseList (F:=F) (C:=C) menu x source target count)
def physical := (J).compile (C:=C) menu x source target count items
theorem component_charges :
    let bill:=(a.physical bounds items).charges
    (∀side,bill.rows side≤N*2^x.h) ∧ bill.selectors≤v.wideSelectorFactor*(2^x.h*x.h) ∧
      bill.workspace≤v.wideSpaceFactor (m+1) (2^ell) ((days).length+1) (v.widePrivateUnit unitCost)
        (v.wideHistoryUnit unitCost)*(2^x.h*x.w) ∧ bill.external≤v.wideExteriorFactor*(2^x.h*x.w) :=
  cpu.native_tariffs ((days).length+1) a.schedule (a.physical bounds items).cut (J).frame.site

def Evaluates (C : ℝ) : Prop := ∀items : PurchaseList (F:=F) (C:=C) menu x source target count,
  Nonempty ((a.physical bounds items).Run)
end SignedSites

variable (v m ell short δ ξ unitCost)
local notation "eligible" x:arg N:arg =>v.ParentFullCPUs m ell short u δ ξ unitCost N x
local notation "hardwareAtCost" C:arg =>HardwareAt (F:=F) (k:=k) (M:=v.radius) (κ:=κ) (A:=A) (u:=u)
  (δ:=δ) (ξ:=ξ) (n:=m) (attempts:=v.wideJobs) (ell:=ell) v.stage_positive short C

/-- Price and mount the same gate pair at every eligible parent for every
purchased near/far compactor. Only the signed site rows require a separate
cell estimate; rows, selectors, common data and exposed bits are already
priced by the concrete two-program mount. -/
theorem hardware_of_signed_sites (hu : TaggedWidthProfile.Admissible s u) (C K b : ℝ)
    (price : 0≤K) (power : 0≤b)
    (assembly : ∀ᶠx : WideParent κ A in WideParent.large κ A,
      ∀N (cpu : eligible x N) (room : cpu.SiteRoom),
      ∃ a : SignedSites v m ell short δ ξ unitCost cpu,a.Evaluates room C ∧
        (((a.installed room).frame.site.cells+(a.installed room).frame.site.internal:ℕ):ℝ)≤
          K*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^b)) : hardwareAtCost C := by
  obtain ⟨N,cpus⟩:=v.cofinal_parent_full_cpus (κ:=κ) (A:=A) m ell short δ ξ unitCost hu
  let Good (x:WideParent κ A):=∃(cpu:eligible x N)(ok:cpu.SiteRoom)
    (a:SignedSites v m ell short δ ξ unitCost cpu), a.Evaluates ok C ∧
    (((a.installed ok).frame.site.cells+(a.installed ok).frame.site.internal:ℕ):ℝ)≤
      K*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^b)
  have often : ∀ᶠx in WideParent.large κ A,Good x:=by
    filter_upwards [cpus,ParentFullCPUs.cofinal_site_room (v:=v) (m:=m) (ell:=ell) (short:=short)
      (u:=u) (δ:=δ) (ξ:=ξ) (unitCost:=unitCost),assembly] with x pair fits complete
    obtain ⟨mountedCPU⟩:=pair
    obtain ⟨a,run,cost⟩:=complete N mountedCPU (fits N mountedCPU)
    exact ⟨mountedCPU,fits N mountedCPU,a,run,cost⟩
  let cpu (x) (e:Good x):eligible x N:=e.choose
  let room (x) (e:Good x):(cpu x e).SiteRoom:=e.choose_spec.choose
  let signedFrames (x) (e:Good x):SignedSites v m ell short δ ξ unitCost (cpu x e):=e.choose_spec.choose_spec.choose
  let build (x) (e:Good x):=(signedFrames x e).installed (room x e)
  refine ⟨N,Good,often,build,(fun x e=>((cpu x e).first,(cpu x e).paid)),?_,?_,?_⟩
  · exact fun x e=>(cpu x e).siteFrame_installed (room x e) (signedFrames x e).schedule
      (signedFrames x e).enter (signedFrames x e).finish (signedFrames x e).step
  · exact fun x e=>e.choose_spec.choose_spec.choose_spec.1
  · intro j notCut notSocket notFlag
    cases j with
    | flag => exact (notFlag rfl).elim
    | cut i => exact (notCut i rfl).elim
    | socket i => exact (notSocket i rfl).elim
    | site =>
      exact ⟨K,b,price,power,Filter.Eventually.of_forall (fun x e _=>e.choose_spec.choose_spec.choose_spec.2)⟩
    | rows side =>
      refine ⟨N,0,by positivity,le_rfl,Filter.Eventually.of_forall (fun x e items=>?_)⟩
      have charge := (Nat.cast_le (α:=ℝ)).mpr (((signedFrames x e).component_charges (room x e) items).1 side)
      simp only [SignedSites.physical,build,wideWindowMenu,WidePhysicalBill.Part.fee,WidePhysicalBill.Part.scale,Real.rpow_zero,mul_one,
        Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at charge ⊢
      exact charge
    | selectors =>
      refine ⟨v.wideSelectorFactor,0,by positivity,le_rfl,Filter.Eventually.of_forall (fun x e items=>?_)⟩
      have charge := (Nat.cast_le (α:=ℝ)).mpr ((signedFrames x e).component_charges (room x e) items).2.1
      simp only [SignedSites.physical,build,wideWindowMenu,WidePhysicalBill.Part.fee,WidePhysicalBill.Part.scale,Real.rpow_zero,mul_one,
        Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at charge ⊢
      exact charge
    | workspace =>
      refine ⟨v.wideSpaceFactor (m+1) (2^ell) ((days).length+1) (v.widePrivateUnit unitCost)
        (v.wideHistoryUnit unitCost),0,by positivity,le_rfl,Filter.Eventually.of_forall (fun x e items=>?_)⟩
      have charge := (Nat.cast_le (α:=ℝ)).mpr ((signedFrames x e).component_charges (room x e) items).2.2.1
      simp only [SignedSites.physical,build,wideWindowMenu,WidePhysicalBill.Part.fee,WidePhysicalBill.Part.scale,Real.rpow_zero,mul_one,
        Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at charge ⊢
      exact charge
    | external =>
      refine ⟨v.wideExteriorFactor,0,by positivity,le_rfl,Filter.Eventually.of_forall (fun x e items=>?_)⟩
      have charge := (Nat.cast_le (α:=ℝ)).mpr ((signedFrames x e).component_charges (room x e) items).2.2.2
      simp only [SignedSites.physical,build,wideWindowMenu,WidePhysicalBill.Part.fee,WidePhysicalBill.Part.scale,Real.rpow_zero,mul_one,
        Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at charge ⊢
      exact charge

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
