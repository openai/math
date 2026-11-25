import OAI.Hierarchy.TaggedWideBranchRoleMap
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


open HistoryRoles.BranchRoles
variable {X:Type} (slot:Event→WireTelescope.CalendarTape.Slot X) (initial:X)
local notation "cursor" => Prefix.Cursor slot es initial
local notation "tree" => Prefix.cursorSlot (slot:=slot) (events:=es) (x₀:=initial)
local notation "root" => (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix slot es initial es initial)
local notation "startAt" => Prefix.atCursor root
variable (π : Equiv.Perm (Fin (2^x.h))) (wire : cursor→Widths K)
    (possible : ∀c:cursor,Nonempty (Path slot c.todo c.mem))
    (dictionary : ∀j:Path slot es initial,BranchRoles v.sampler π v.depth roles wire j)
    (j:Path slot es initial)
local notation "selected" => Prefix.histories root j
local notation "pins" => BranchRoles.cells possible dictionary j
local notation "book" => dictionary j

/-- The five native circuit factors use the same address space. This is the
history-mask factor at the selected cursor, obtained from the original role pages. -/
theorem wide_numbered_history_mask (low : WideParent.columnBits view≤(G).W+1) {n:ℕ}
    (raw : Fin n→ProtocolRAMEmit.Row) (positive : Fin n→Prop) (stage : Fin n→ℕ)
    (ord : {i:Fin n//¬positive i}≃Priv)
    (b : ∀t,Installed F (dir).groups ports (2^ell) x.w m (key t).2 (atScale positive stage (key t).1 raw))
    (ex : Ex→Bool) (sel : Se→Bool) (final snapshot:Memory (G).W)
    (a : (i:Fin n)→Fin (2^(raw i).width)) (hist : H→Bool)
    (capWord: view<2^(G).W) (rows:ℕ)
    (pages:∀t:Fin ((es).length+1),DatedRoleSheets.roleFact rows v.sampler π v.depth (book).mark
      (book).exclusive (book).order (base t) ((book).bits t) (book).ident snapshot 0)
    (keep:∀t (r:R),final (base t+1+(index r).val)=snapshot (base t+1+(index r).val)) :
    TypedWiring.value (v.wideHistoryGate (Ex:=Ex) (Se:=Se) x m ell short u δ ξ unitCost lim low)
      (CalendarTerms.readPins (B:=G) (CalendarTerms.privateWorkspace key ord cap roles (dir).groups ports
        (2^ell) ((es).length+1) view x.w) ex sel ((G).terminal final)
        (nativePins («view»:=view) key raw positive stage b (cap ∘ ord) a hist)) =
      if ∀i,hist i=true→i∈Set.range (timelineFin tree wire pins es startAt selected) then 1 else 0 := by
  have bound (r:R):roles r<2^(G).W :=
    (HistoryRoles.ceiling_le v.sampler v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) x.w r).trans_lt capWord
  let observed:=fun t:Fin ((es).length+1)=>BranchRoles.observed possible dictionary j t rows (base t)
    (G).W snapshot final bound (pages t) (keep t)
  exact v.wide_history_nativePins x m ell short u δ ξ unitCost lim low raw positive stage ord b tree wire pins
    startAt selected ex sel final (fun _=>final) a hist (fun _ _=>rfl) (fun t=>(observed t).1)
    (fun t=>(observed t).2)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
