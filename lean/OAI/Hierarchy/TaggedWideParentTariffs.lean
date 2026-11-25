import OAI.Hierarchy.TaggedWideParentCPUs
import OAI.Hierarchy.TaggedWideOriginalPins
import OAI.Hierarchy.TaggedWideWorkspaceTariff
import OAI.Hierarchy.TaggedWideGuardedBill

namespace OAI
/-! # The original records charged by the installed native parent frame -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PhysicalTerm
open HistoryRoles ReportSockets Tagged TaggedPrune WideControlJoin WireTelescope
open ThreeFlat Routing
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A)
    (m ell short unitCost dates : ℕ)

local notation "geom" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "priv" => fun _ : (v.widePlacement x.h x.w).catalogue.Private (v.wideOrder x.h x.w) =>
  v.widePrivateUnit unitCost*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) x.w
local notation "dir" => WideMemory.dir x.h v.W k v.wideJobs
local notation "ports" => WideMemory.H x.h v.W k v.wideJobs

/-- The original public menu, private edges, dated role widths and reported view,
with the literal width and slot count from the installed parent format. -/
abbrev parentShared := CalendarTerms.Shared (geom).index priv roles (dir).groups ports (2^ell) dates
  (v.wideHistoryUnit unitCost*x.w) x.w

/-- The RAM word-height bound in the mounted format pays for the actual calendar
selector slots at that height, including the original tag tape. -/
theorem parent_selector_bits {x : WideParent κ A} (ready : CountedReady v x.h x.w v.maxBits)
    (age : v.wideStockHeight≤ x.h) (large : v.programRoomHeight≤ x.h) :
    CalendarTape.bits (v.wideSelector x.h x.w age ready.credit ready.size_le).format.slot (events v.mesh)≤
      v.wideSelectorFactor*(2^x.h*x.h) := by
  unfold programRoomHeight at large
  have pos : 0<x.h:=by omega
  have clock : 2*(rounds (2^v.W)+1)+3+rounds (2^v.W)*Native.stride (2^v.W) copies≤ x.h:=by omega
  have sel : x.h*2^x.h+CalendarTape.bits
      (v.wideSelector x.h x.w age ready.credit ready.size_le).format.slot (events v.mesh)≤
        v.wideSelectorFactor*(2^x.h*x.h) := by
    unfold wideSelector
    apply v.original_selectors <;> assumption
  omega

/-- A procedure gate's table bound uses all initial, fuel and output rows. -/
theorem parent_mounted_rows {h N : ℕ} {gates : Gate×Gate} {first paid : Mounted h N}
    (same : gates=(first.gate,paid.gate)) (a : first.rows≤ N*2^h) (b : paid.rows≤ N*2^h) :
    ∀ side : Bool,(if side then gates.2.S+(gates.2.f+gates.2.u) else gates.1.S+(gates.1.f+gates.1.u))≤ N*2^h := by
  rintro (_|_)
  · exact (congrArg (fun z : Gate×Gate=>z.1.S+(z.1.f+z.1.u)) same).trans_le a
  · exact (congrArg (fun z : Gate×Gate=>z.2.S+(z.2.f+z.2.u)) same).trans_le b

namespace ParentCPUs
variable {v x m ell short unitCost} {u : ℝ→ℝ} {δ ξ : ℝ} {N : ℕ}
    (cpu : v.ParentCPUs m ell short u δ ξ unitCost N x)
local notation "d" => 2^v.W
local notation "g" => v.wideDated x.h x.w ell unitCost
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "G" => v.wideGates x.h x.w v.maxBits l S cpu.room
local notation "D" => v.parentShared x m ell short unitCost dates
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
local notation "es" => events v.mesh
local notation "R" => CatalystArchive.fuel v.mesh*x.w
variable (Z : CalendarTerms F x.h (2^v.W) k x.w (CatalystArchive.fuel v.mesh*x.w) v.radius 1
  (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot (events v.mesh)
  (v.wideOrigin x.h x.w (v.wideInstalledSize x m ell unitCost (v.wideDated x.h x.w ell unitCost))
    (v.wideInstalledHeader x m ell short u δ ξ unitCost (v.wideDated x.h x.w ell unitCost)
      (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0))))
local notation "rout" => Z.nativeRouting D
local notation "E" => OpenPins x.h x.w (rout).catalyst
local notation "V" => SitePins E (Fin (rout).selectors) D (G).2

/-- These are charges of the original native circuits on any site network and
cut bank with the installed pin type. The site and cuts have their own separately
measured bills. -/
theorem native_tariffs {n : ℕ} (cuts : Fin n→CutFormat F V) (site : BitNetwork F (Fintype.card V)) :
    let bill:=nativeCharges rout (G).1 (G).2 cuts site
    (∀side,bill.rows side≤ N*2^x.h) ∧ bill.selectors≤ v.wideSelectorFactor*(2^x.h*x.h) ∧
      bill.workspace≤ v.wideSpaceFactor (m+1) (2^ell) dates (v.widePrivateUnit unitCost)
        (v.wideHistoryUnit unitCost)*(2^x.h*x.w) ∧ bill.external≤ v.wideExteriorFactor*(2^x.h*x.w) := by
  intro bill
  refine ⟨parent_mounted_rows cpu.same cpu.firstRows cpu.paidRows,
    v.parent_selector_bits cpu.ready cpu.age cpu.large,?_,?_⟩
  · change Fintype.card D≤ _
    simpa only [Fintype.card_fin] using v.original_workspace (geom).index x.h x.w (2^ell) dates unitCost
  · exact v.original_exterior x.h x.w x.property.1.2.1

end ParentCPUs
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
