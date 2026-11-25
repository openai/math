import OAI.Hierarchy.TaggedWideParentTariffs
import OAI.Hierarchy.TaggedWideParentFullCPUs
import OAI.Hierarchy.TaggedWideMaskWord

namespace OAI
/-! # Charges and paid column widths on the genuine appended overflow gate -/

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

namespace ParentFullCPUs
variable {v x m ell short unitCost} {u : ℝ→ℝ} {δ ξ : ℝ} {N : ℕ}
    (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
local notation "d" => 2^v.W
local notation "g" => v.wideDated x.h x.w ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "G" => v.wideFullGates x m ell short u δ ξ unitCost cpu.room
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

/-- Every fixed paid width column fits the word of the appended native gate
eventually, uniformly over the mounted parent and the size coefficient. -/
theorem cofinal_column_room (K : ℕ) : ∀ᶠ x : WideParent κ A in WideParent.large κ A,
    ∀ (N : ℕ) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x),
      WideParent.columnBits (K*x.w)≤ (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2.W := by
  filter_upwards [WideParent.columnBits_wordBits (κ:=κ) (A:=A) K] with x room
  exact fun _ _=>room (2^v.W) copies

theorem cofinal_mounted_column_room (K : ℕ) : ∀ᶠ x : WideParent κ A in WideParent.large κ A,
    ∀ (N : ℕ) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x),
      WideParent.columnBits (K*x.w)≤ cpu.paid.W := by
  filter_upwards [cofinal_column_room (v:=v) (κ:=κ) (A:=A) (m:=m) (ell:=ell) (short:=short)
    (u:=u) (δ:=δ) (ξ:=ξ) (unitCost:=unitCost) K] with x paid
  intro N cpu
  exact (paid N cpu).trans_eq (congrArg (fun z : Gate×Gate=>z.2.W) cpu.same)

end ParentFullCPUs
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
