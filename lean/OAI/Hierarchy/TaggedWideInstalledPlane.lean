import OAI.Hierarchy.TaggedWideCalendarPlane
import OAI.Hierarchy.TaggedWideParentFullTariffs
import OAI.Hierarchy.TaggedWideCalendarFrame

namespace OAI
/-! # Common output labels and the physical decoder in the full paid parent -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ThreeFlat Routing
open ProbeStage ProbeStage.ReportSockets ProbeStage.CoreBoard PhysicalTerm HistoryRoles Tagged TaggedPrune WideStack WideStack.Leaf
open TaggedShorterBudget Tagged.WideControlJoin
open scoped Classical BigOperators
variable {F Ex Se : Type} [Field F] [Fintype Ex] [Fintype Se] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ)
    (δ ξ : ℝ) (unitCost : ℕ) (lim : v.FullGateRoom x m ell short u δ ξ unitCost)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost lim).2
local notation "menu" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "key" => (menu).index
local notation "dir" => WideMemory.dir x.h v.W k v.wideJobs
local notation "ports" => WideMemory.H x.h v.W k v.wideJobs
local notation "dates" => (events v.mesh).length+1
local notation "view" => v.wideHistoryUnit unitCost*x.w
local notation "privateWidth" => v.widePrivateUnit unitCost*x.w
local notation "privateType" => (v.widePlacement x.h x.w).catalogue.Private (v.wideOrder x.h x.w)
local notation "cap" => fun _:privateType=>privateWidth
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) x.w
local notation "history" => Fin (dates*Fintype.card ((r:Public v.sampler x.h v.W k v.wideJobs)×Fin (roles r)))
local notation "output" => ((Fin (dir).groups×Fin ports)× Fin view)

def widePlane := planeNet (F:=F) (Ex:=Ex) (Se:=Se) (H:=history)
  (groups:=(dir).groups) («ports»:=ports) (lanes:=2^ell) («view»:=view) (w:=x.w) key cap G

local notation "net" => v.widePlane (Ex:=Ex) (Se:=Se) x m ell short u δ ξ unitCost lim

theorem wide_plane_fee : (net).cells+(net).internal≤ Fintype.card output*(48*(2*(m+1))+98) := by
  simpa only [widePlane, Fintype.card_fin] using
    (planeNet_cost (F:=F) (Ex:=Ex) (Se:=Se) (H:=history) (groups:=(dir).groups) («ports»:=ports)
      (lanes:=2^ell) («view»:=view) (w:=x.w) key cap G)

theorem wide_plane_decode {E : Type} [Fintype E] {N : ℕ}
    (ord : E≃privateType) (records : Fin (m+1)→Fin N→ProtocolRAMEmit.Row)
    (b : ∀t,Installed F (dir).groups ports (2^ell) x.w m (key t).2 (records t))
    (ext:Ex→Bool) (sel:Se→Bool) (seen:(G).Seen→Bool)
    (z:∀t,(banks b t).Slots) (y:PrivatePorts (cap ∘ ord)) (hist:history→Bool) (printed:output→Bool) :
    TypedWiring.value net (CalendarTerms.readPins (B:=G)
      (CalendarTerms.privateWorkspace key ord cap roles (dir).groups ports (2^ell) dates view x.w)
      ext sel seen (write (banks b) (cap ∘ ord) z y hist printed)) =
      TypedWiring.value (decoder (F:=F) (groups:=(dir).groups) («ports»:=ports) (lanes:=2^ell)
        («view»:=view) (w:=x.w) key) (Sum.elim (voltage (banks b) z) printed) := by
  rw [widePlane,planeNet,WideHost.onPins_value]
  apply congrArg (TypedWiring.value _)
  funext i
  cases i <;> rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
