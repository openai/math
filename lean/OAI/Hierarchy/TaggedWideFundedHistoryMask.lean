import OAI.Hierarchy.TaggedWidePathRoleRead
import OAI.Hierarchy.TaggedWideNumberedHistoryMask
import OAI.Hierarchy.TaggedWideBranchRoleHeight
import OAI.Hierarchy.TaggedWideNativeHistoryCells
import OAI.Hierarchy.TaggedWideInstalledHistory
import OAI.Hierarchy.TaggedWideDatedHistoryRange
import OAI.Hierarchy.TaggedWideInstalledPlane
import OAI.Hierarchy.TaggedWideCalendarReceipt

namespace OAI
/-! # The chronological mask on the same data pins as the funded cut cells -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat Routing Diagonal TraceWords
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.CoreBoard PhysicalTerm HistoryRoles
open Tagged TaggedPrune TaggedShorterBudget WideStack WideStack.Leaf WideControlJoin WideCalendarSites
open WireTelescope CalendarTape
open scoped Classical Fin.CommRing BigOperators
variable {F Ex Se : Type} [Field F] [Fintype Ex] [Fintype Se] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A)
    (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    (lim : v.FullGateRoom x m ell short u δ ξ unitCost)
local notation "es" => events v.mesh
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost lim).2
local notation "menu" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "key" => (menu).index
local notation "dir" => WideMemory.dir x.h v.W k v.wideJobs
local notation "ports" => WideMemory.H x.h v.W k v.wideJobs
local notation "view" => v.wideHistoryUnit unitCost*x.w
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost dated
local notation "R" => Public v.sampler x.h v.W k v.wideJobs
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) x.w
local notation "H" => Fin (((es).length+1)*Fintype.card ((r:R)×Fin (roles r)))
local notation "Priv" => (v.widePlacement x.h x.w).catalogue.Private (v.wideOrder x.h x.w)
local notation "cap" => fun _:Priv=>v.widePrivateUnit unitCost*x.w
local notation "K" => siteLast x.h (2^v.W) k+1
local notation "index" => fun r:R=>(shelfSlot v.sampler r : Fin (dated).roleWords)
local notation "base" => fun t : Fin ((es).length+1)=>(dated).roleStart S t



open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ReportSockets
open HistoryRoles.BranchRoles
variable (height:v.BranchRoleHeight x.h x.w) (rate:v.sharpPaidUnit≤unitCost)
    (π:Equiv.Perm (Tagged.Row x.h)) (seed:Boot.Tape x.h (2^v.W))
local notation "reader" => v.wideSelector x.h x.w height.age height.credit height.small
local notation "slots" => (reader).format.slot
local notation "origin" => v.wideOrigin x.h x.w S seed π
local notation "extent" => (v.wide_installed_tape_bounds x m ell unitCost dated).2.2
variable (path:Path slots es origin)
local notation "rawPath" => (reader).format.windows.header es (encode slots es origin path) seed
local notation "fit" => height.funded_aperture S unitCost extent rate
local notation "wire" => WireTelescope.CalendarTape.Prefix.atWidth («slot»:=slots) (events:=es) (x₀:=origin) («S»:=siteLast x.h (2^v.W) k+1) (fun {_ _} c => v.wideCursorWidth x.h x.w S π seed height.age height.credit height.small c)
local notation "rows" => fun j=>v.widePathRoles x.h x.w S π seed height.age height.credit height.small
  extent height.report height.wordRoom j unitCost height.replay height.measure fit
local notation "possible" => fun c=>v.wide_funded_continuation x.h x.w S
  ((v.wide_funded_extent x.h x.w v.maxBits).trans extent) π seed height.age height.credit height.small c.path
local notation "root" => (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix slots es origin es origin)
local notation "tree" => WireTelescope.CalendarTape.Prefix.cursorSlot («slot»:=slots) (events:=es) (x₀:=origin)
local notation "wiremap" => v.widePathCells x.h x.w S π seed height.age height.credit height.small
  extent height.report height.wordRoom path unitCost height.replay height.measure fit
local notation "states" => timelineFin tree wire wiremap es (WireTelescope.CalendarTape.Prefix.atCursor root) (WireTelescope.CalendarTape.Prefix.histories root path)
local notation "receipt" => v.wide_reported_path_funded_rows x.h x.w S π seed height.age height.credit height.small
  extent height.report height.wordRoom path
local notation "w" => Native.wordBits x.h (2^v.W) Native.copies
local notation "run" => v.wide_funded_run_at x.h x.w v.radius π.symm rawPath v.maxBits S extent
  (Classical.choose receipt) height.credit height.small (0:Word w)
local notation "settled" => (Classical.choose_spec run).1
/-- The original role publication and its genuine lower frame at this one
native return are sufficient to evaluate the entire chronological room mask. -/
theorem widePath_history_mask (low:WideParent.columnBits view≤(G).W) {n:ℕ}
    (raw:Fin n→ProtocolRAMEmit.Row) (positive:Fin n→Prop) (stage:Fin n→ℕ)
    (ord:{i:Fin n//¬positive i}≃Priv)
    (b : ∀t,Installed F (dir).groups ports (2^ell) x.w m (key t).2 (atScale positive stage (key t).1 raw))
    (ex:Ex→Bool) (sel:Se→Bool) (earlier final:Memory (G).W)
    (a : (i:Fin n)→Fin (2^(raw i).width)) (hist:H→Bool)
    (published:v.widePathOriginalDateFields x.h x.w S π seed height.age height.credit height.small
      extent height.report height.wordRoom path ell unitCost S earlier)
    (frame:∀i,i<(dated).rolesEnd S→final i=earlier i) :
    TypedWiring.value (v.wideHistoryGate (Ex:=Ex) (Se:=Se) x m ell short u δ ξ unitCost lim (Nat.le_succ_of_le low))
      (CalendarTerms.readPins (B:=G) (CalendarTerms.privateWorkspace key ord cap roles (dir).groups ports
        (2^ell) ((es).length+1) view x.w) ex sel ((G).terminal final)
        (nativePins («view»:=view) key raw positive stage b (cap ∘ ord) a hist)) =
      if ∀i,hist i=true→i∈Set.range states then 1 else 0 := by
  have word:view<2^(G).W := (WideParent.column_lt view).trans_le (Nat.pow_le_pow_right (by decide) low)
  let fields:=v.wide_path_role_fields x.h x.w S π seed height.age height.credit height.small extent
    height.report height.wordRoom path unitCost height.replay height.measure fit ell S earlier final published frame
  exact v.wide_numbered_history_mask x m ell short u δ ξ unitCost lim slots origin π.symm wire possible rows path
    (Nat.le_succ_of_le low) raw positive stage ord b ex sel final final a hist word (dated).physical
    (fun t=>fields t 0) (fun _ _=>rfl)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
