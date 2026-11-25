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
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat Routing Diagonal TraceWords
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.CoreBoard PhysicalTerm HistoryRoles
open Tagged TaggedPrune TaggedShorterBudget WideStack WideStack.Leaf WideControlJoin WideCalendarSites
open WireTelescope CalendarTape ProbeStage.ReportSockets
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

/-- The final nine-word reporter, the cut banks and all hidden choices share one
chronological bit dictionary. The native role page is read at its original address
after the rest of the paid program has executed. -/
theorem wide_history_nativePins (low : WideParent.columnBits view≤(G).W+1) {n : ℕ}
    (raw : Fin n→ProtocolRAMEmit.Row) (positive : Fin n→Prop) (stage : Fin n→ℕ)
    (ord : {i:Fin n//¬positive i}≃Priv)
    (b : ∀t,Installed F (dir).groups ports (2^ell) x.w m (key t).2 (atScale positive stage (key t).1 raw))
    {X:Type} (slot : Event→WireTelescope.CalendarTape.Slot X) (wire : X→Widths K)
    (cells : ∀s,((i:Fin K)×SiteBit (wire s) i)↪((r:R)×Fin (roles r)))
    (start : X) (path : Path slot es start) (ex : Ex→Bool) (sel : Se→Bool)
    (final : Memory (G).W) (reports : Fin ((es).length+1)→Memory (G).W)
    (a : (i:Fin n)→Fin (2^(raw i).width)) (hist : H→Bool)
    (observed : ∀t (r:R),final (base t+1+(index r).val)=reports t (base t+1+(index r).val))
    (word : ∀t (r:R),(reports t (base t+1+(index r).val)).val≤roles r)
    (states : ∀t (z:(r:R)×Fin (roles r)), z∈Set.range (cells (boundaryState slot es start path t)) ↔
      z.2.val<(reports t (base t+1+(index z.1).val)).val) :
    TypedWiring.value (v.wideHistoryGate (Ex:=Ex) (Se:=Se) x m ell short u δ ξ unitCost lim low)
      (CalendarTerms.readPins (B:=G) (CalendarTerms.privateWorkspace key ord cap roles (dir).groups ports
        (2^ell) ((es).length+1) view x.w) ex sel ((G).terminal final)
        (nativePins («view»:=view) key raw positive stage b (cap ∘ ord) a hist)) =
      if ∀i,hist i=true→i∈Set.range (timelineFin slot wire cells es start path) then 1 else 0 := by
  apply v.wide_history_read x m ell short u δ ξ unitCost lim low slot wire cells start path final _ hist
  · intro t r j
    rfl
  · intro t r
    rw [observed]
    exact (word t r).trans (HistoryRoles.ceiling_le v.sampler v.mesh unitCost v.keepLimit
      (CatalystArchive.fuel v.mesh) x.w r)
  · intro t z
    rw [observed]
    exact states t z
  · intro i
    rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
