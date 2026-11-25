import OAI.Hierarchy.TaggedWideFundedSiteCuts
import OAI.Hierarchy.TaggedWideRankedReceipt
import OAI.Hierarchy.TaggedWideFundedSelectedOutput

namespace OAI
/-! # Individual endpoint observations on one common paid party embedding -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open AdaptiveProbe TaggedPrune Tagged WireTelescope WireTelescope.CalendarTape ProtocolRAM.Calendar
open ProtocolStackContraction TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open WideStack WideStack.Leaf WideCalendarSites WideControlJoin
open scoped Classical BigOperators
set_option quotPrecheck false

variable {F : Type} [Field F] {X : Type} {z d k w R M den : ℕ}
    {slots : Event→Slot X} {es : List Event} {state : Equiv.Perm (Row z)→X}
    (Z : CalendarTerms F z d k w R M den slots es state) {L groups ports lanes view m n : ℕ}
    {S : Type} [Fintype S] (key : Fin L ↪ ℕ×ℕ) (B₁ : Gate)
local notation "Rout" => Z.nativeRouting S
open private rankedPins rankedBoard rankedParty from OAI.Hierarchy.TaggedWideRankedReceipt
variable (cut : Fin L→CutFormat F (rankedPins Z B₁ (S:=S)))
    (keep pad privateGate plane timeline : Net F (rankedPins Z B₁ (S:=S)))
    (E T₁ : Fin (siteLast z d k+1)→Net F (rankedPins Z B₁ (S:=S)))
    (row : Fin (siteLast z d k+1)→Fin es.length→Net F (rankedPins Z B₁ (S:=S)))
    (perm : Equiv.Perm (Row z)) (i : Fin ((Z.nativeRouting S).count perm))
    (ext : OpenPins z w (Z.nativeRouting S).catalyst→Bool)
    (sel : Fin (Z.nativeRouting S).selectors→Bool) (seen : B₁.Seen→Bool)
local notation "A₀" => (WireTelescope.CalendarTape.Prefix.start :
  WireTelescope.CalendarTape.Prefix slots es (state perm) es (state perm))
local notation "C" => (Prefix.cursorSlot (slot:=slots) (events:=es) (x₀:=state perm))
local notation "V₀" => Prefix.atCursor A₀
local notation "ws" => Prefix.atWidth (Z.width perm)
local notation "step" => Prefix.atStep (Z.width perm) (Z.operator perm)
local notation "rep" => cursorReport perm (Z.width perm) (Z.reported perm)
local notation "branch" => (Prefix.histories A₀) ((Fintype.equivFin (Path slots es (state perm))).symm i)
local notation "raw" => (rep branch).rows
local notation "Keep" => ((Rout).links ⟨perm,i⟩).Keep (2^z)
local notation "trace" => placedBits C ws es V₀ branch
local notation "γ" => fun t:Fin L=>(key t).2
local notation "P" => (Fin groups×Fin ports)×Fin view


variable (r : RankedRows (F:=F) key S groups ports lanes w m n view (rankedBoard Z (S:=S) perm i))
    (place : rankedParty Z (S:=S) perm i ↪ Fin n)

inductive EndpointField
  | historyMask | first | finish | steps

def RankedRows.Check (field : EndpointField) : Prop :=
  match field with
  | .historyMask => ∀a h,TypedWiring.value timeline (readPins (B:=B₁) r.numbering ext sel seen
    (nativePins (view:=view) key raw r.positive r.stage r.installed r.cap a h))=
      if ∀j,h j=true→j∈Set.range place then 1 else 0
  | .first => ∀a (q : SiteChoices C ws es V₀ branch) s,TypedWiring.value (E s) (readPins (B:=B₁) r.numbering ext sel seen
    (nativePins (view:=view) key raw r.positive r.stage r.installed r.cap a (trace place q))) =
    entry perm ws V₀ (Z.head perm) s (fun t=>ext (routingPort t.val)) (q s).1
  | .finish => ∀a (q : SiteChoices C ws es V₀ branch) s,TypedWiring.value (T₁ s) (readPins (B:=B₁) r.numbering ext sel seen
    (nativePins (view:=view) key raw r.positive r.stage r.installed r.cap a (trace place q))) =
    (rep branch).finish s (WideCalendarSites.last C ws s es V₀ branch (q s).1 (q s).2) ((rep branch).ports a s)
  | .steps => ∀a (q : SiteChoices C ws es V₀ branch) s,Reads C ws step s es V₀ branch (q s).1 (q s).2
    (fun j=>TypedWiring.value (row s j) (readPins (B:=B₁) r.numbering ext sel seen
      (nativePins (view:=view) key raw r.positive r.stage r.installed r.cap a (trace place q))))

theorem RankedRows.endpoints_of_checks
    (valid : ∀f,RankedRows.Check Z key B₁ timeline E T₁ row perm i ext sel seen r place f) :
    RankedRows.Endpoints Z key B₁ timeline E T₁ row perm i ext sel seen r place :=
  ⟨valid .historyMask, valid .first, valid .finish, valid .steps⟩

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows CatalystArchive
open Tagged Tagged.WideStack TaggedShorterBudget TaggedShorterSupergroups ProtocolRAMEmit
open ProtocolRAMReportedPorts PurchaseFrozen
open scoped Classical BigOperators
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option cleanup.letToHave false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (tapeSize : ℕ)
    (π : Equiv.Perm (Fin (2^x.h))) (input : Boot.Tape x.h (2^v.W)) (m ell short unitCost : ℕ)
local notation "b" => (v.widePlacement x.h x.w).catalogue
local notation "jobs" => v.wideJobs
local notation "geom" => typeMenu κ A v.W m k jobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geom).menu u δ ξ
local notation "slots" => purchaseSlots x.h v.W k jobs ell
local notation "reserve" => fuel v.mesh*x.w
variable (raw : Fin (b).rows→ ProtocolRAMEmit.Row)
    (geometry : Geometry (boardLayout x.h (2^v.W) k x.w reserve) v.radius 1 raw)
    (actual : v.FundedCutRows x.h x.w tapeSize π input raw geometry unitCost)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates x.h v.W k jobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k jobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
open CoreBoard.PhysicalTerm Tagged.WideControlJoin WideCalendarSites HistoryRoles
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune

local notation "days" => events v.mesh
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
variable {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (room : cpu.SiteRoom)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
variable (a : SignedSites v m ell short δ ξ unitCost cpu)
local notation "Z" => a.schedule
local notation "D" => v.parentShared x m ell short unitCost ((days).length+1)
local notation "Ex" => OpenPins x.h x.w ((Z).nativeRouting D).catalyst
local notation "Se" => Fin ((Z).nativeRouting D).selectors
local notation "cap" => v.widePrivateUnit unitCost*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) («W»:=v.W) (k:=k) (attempts:=jobs)
  v.mesh unitCost v.keepLimit (fuel v.mesh) x.w
local notation "n" => ((days).length+1)*Fintype.card ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r))

variable (perm : Equiv.Perm (Tagged.Row x.h)) (i : Fin (((Z).nativeRouting D).count perm))
local notation "branch" => (Fintype.equivFin (Path slot days ((v.wideOrigin x.h x.w size seed) perm))).symm i
local notation "original" => (Z).reported perm branch
local notation "time" => v.wideHistoryGate («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room room.history
local notation "rout" => (Z).nativeRouting D
local notation "accept" => ((rout).links ⟨perm,i⟩).Keep (2^x.h)
local notation "flagAt" => (lay).pruneScratch+(lay).pruneRows
local notation "cursor" => CalendarTape.Prefix.cursorSlot («slot»:=slot) (events:=days) (x₀:=(v.wideOrigin x.h x.w size seed) perm)
local notation "hs" => CalendarTape.Prefix.atCursor (CalendarTape.Prefix.start : CalendarTape.Prefix slot days ((v.wideOrigin x.h x.w size seed) perm)
  days ((v.wideOrigin x.h x.w size seed) perm))
local notation "ws" => CalendarTape.Prefix.atWidth ((Z).width perm)
local notation "branchAt" => CalendarTape.Prefix.histories (CalendarTape.Prefix.start : CalendarTape.Prefix slot days ((v.wideOrigin x.h x.w size seed) perm)
  days ((v.wideOrigin x.h x.w size seed) perm)) branch

variable {v x tapeSize π input m ell short unitCost raw geometry actual prices pricePos buy
  groupsFit metadata lanesFit cpu room a perm i}
variable {mem before initial out : Memory W}
local notation "signedBoard" => RowGeometry x.h (2^v.W) k x.w reserve v.radius 1
variable (same : reportGeometry perm original = (⟨(b).rows,raw,geometry⟩ : signedBoard))
local notation "sameRows" => congrArg
  (fun r : signedBoard => (⟨r.1,r.2.1⟩ : CalendarTerms.RowBoard)) same
local notation "imageType" => FundedCutRows.WindowReceipt v x tapeSize π input m ell short unitCost
  raw geometry actual prices pricePos buy groupsFit metadata lanesFit cpu.room room.purchase mem before initial out
local notation "sourceAt" ok:arg => FundedCutRows.rowData v x tapeSize π input m ell short unitCost
  raw geometry actual prices pricePos buy groupsFit metadata ok lanesFit
local notation "rankAt" ok:arg => CalendarTerms.RankedRows.onBranch Z perm i sameRows (sourceAt ok)
local notation "rankFacts" ex:arg sel:arg ok:arg place:arg => CalendarTerms.RankedRows.Endpoints Z (geom).index G time
  a.enter a.finish a.step perm i ex sel ((G).terminal out) (rankAt ok) place

def FundedCutRows.EndpointCheck (_image : imageType) (ex : Ex→Bool) (sel : Se→Bool)
    (place : PartyBit cursor ws days hs branchAt ↪ Fin n) (field : CalendarTerms.EndpointField) : Prop :=
  ∀ok : geometry.links.Keep (2^x.h), CalendarTerms.RankedRows.Check Z (geom).index G time a.enter a.finish a.step
    perm i ex sel ((G).terminal out) (rankAt ok) place field

theorem FundedCutRows.endpointFacts_of_checks (image : imageType) (ex : Ex→Bool) (sel : Se→Bool)
    (place : PartyBit cursor ws days hs branchAt ↪ Fin n)
    (valid : ∀f,FundedCutRows.EndpointCheck (a:=a) (room:=room) (perm:=perm) (i:=i) same image ex sel place f) :
    FundedCutRows.EndpointFacts (a:=a) (room:=room) (perm:=perm) (i:=i) same image ex sel := by
  intro ok
  exact ⟨place,CalendarTerms.RankedRows.endpoints_of_checks Z (geom).index G time a.enter a.finish a.step perm i ex sel ((G).terminal out) (rankAt ok) place (fun f=>valid f ok)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
