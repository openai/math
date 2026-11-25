import OAI.Hierarchy.ProtocolRAMCatalystSettlement
import OAI.Hierarchy.ProtocolRAMCatalystArchiveDates
import OAI.Hierarchy.ProtocolRAMCatalystArchiveMaster
import OAI.Hierarchy.ProtocolRAMCoreRoutePaid

namespace OAI
/-! # The terminal execution for all actual signed strips issued from the joined boot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard CatalystArchive
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
variable {z W k attempts R K q d count payload edges : ℕ} {S : PurchaseSampler}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "r" => Fintype.card (Slots z D k)
local notation "w" => Native.wordBits z D Native.copies

/-- All typed widths and owners are computed by the original strip selector on its own
input. Header words and core-catalogue data come from the same boot as the input to the run. -/
theorem master_settle (C : Chart w q d) (A : Arena) (L : OwnerLedger) (cashBase : Event→ℕ) (flag : ℕ) (raw initial : Memory w)
    (date : Dates C initial L cashBase count payload) (feedZero : ∀b,L.rows (.feed b)=0) (s : Sink r edges) (src : ℕ)
    (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (pos : 0<count)
    (countRoom : count<2^w) (reserveFits : fuel C.mesh*payload<2^w)
    (p : Recipes) (π : Equiv.Perm (Fin (2^z))) (place : Site z D k→Fin K)
    (B : Mount (S:=S) π place edges) (order : Fin R≃Edges S z D k) (o : Orders z D k)
    {M K₀ H depth : ℕ} {groups : Fin K₀≃AllGroups z D}
    {packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k attempts)) H}
    {v : BoughtSockets.Directory attempts}
    (seen : Seen order M groups packed v depth π initial)
    (stopEarly : stop S z W k attempts depth K₀ packed.groups H R≤A.first)
    (physical : ∀e,(B.row e).val=(order.symm e).val)
    (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→Fin count)
    (sRoom : SinkSpace s w) (archRoom : Room C.mesh A L a s.banks count (recordCount C.mesh (issued date)) w)
    (routeInput : (ReserveUse.word a s.banks).Fits w s.banks.kind.base)
    (flagEnd : A.endAddress C.mesh≤flag) (mounted : Calendar.mounted C (events C.mesh) initial)
    (floor : ∀t u,u<A.base C.mesh t→protected C u t)
    (spans : ∀e∈events C.mesh,L.rows e≤L.arena.stride)
    (args : ∀t : Fin (events C.mesh).length,(L.term ((events C.mesh).get t)).Fits w (A.base C.mesh ((events C.mesh).get t)))
    (paidInputs : ∀e∈events C.mesh,(L.term e).Fits w s.banks.width.base)
    (amountSpan : ∀t : Fin (events C.mesh).length,∀j : Fin (atTime C.mesh (issued date) t).rows,
      a.history.base+cashBase ((events C.mesh).get t)+j.val<A.base C.mesh ((events C.mesh).get t)+A.stride)
    (flagFit : (historyFlag C (events C.mesh)).Fits w flag) (flagBound : flag+1<2^w)
    (widthBound : s.banks.width.base+edges<2^w)
    (rowBound : L.arena.endAddress C.mesh<2^w)
    (safe : Safe (source S z W k attempts depth K₀ packed.groups H R) S z W k attempts w s.banks.kind.base)
    (space : p.kind.Fits w s.banks.kind.base ∧ p.mode.Fits w s.banks.kind.base ∧ p.operand.Fits w s.banks.kind.base)
    (rowsFit : 2*r≤2^w) (menu : Fintype.card (Actions N k)≤2^w)
    (kindCap : 2*r≤ s.banks.kind.size) (indexCap : 2*r≤ s.banks.index.size)
    (ki : s.banks.kind.base+2*r≤ s.banks.index.base) (end_ : s.banks.index.base+2*r<2^w)
    (publicROM : StaticAt a (rowOnly C.mesh (declaredRows C.mesh L) (L.arena.base C.mesh)) (rowOnly C.mesh (declaredRows C.mesh L) cashBase)
      p o ci (fun i=>(cj i).val) s.owners edges raw initial)
    (recipeLow : ∀f,(which p f).base+(which p f).size≤A.first)
    (ownerLow : s.owners.base+s.owners.size≤A.first) (ownersBefore : s.owners.base+s.owners.size≤ s.banks.kind.base) :
    let chk := checkedOut C flag initial
    let paid := PaidWidths.output s.banks.width edges src ss chk
    let old := result (L.scans C.mesh count) paid
    let routes := stages s.banks p (source S z W k attempts depth K₀ packed.groups H R) S z W k attempts
    let out := result routes old
    let owners := nativeSite L C.mesh (issued date) pos chk
    let bits := debit C.mesh (issued date)
    let reserve := fuel C.mesh*payload
    let final := ReserveUse.output a s.banks reserve owners bits out
    let _id := sourceAt C.mesh (issued date) (L.arena.base C.mesh)
    let _amount := sourceAt C.mesh (issued date) cashBase
    PaidWidths.Mounted s.banks.width edges src ss chk →
    Whole.Reconciliation s a reserve owners bits (enum B o) ci cj out ∧
      (terminal C L routes flag s src ss a count (recordCount C.mesh (issued date)) reserve).Exec initial
        (s.output final (enum B o) ci (fun i=>(cj i).val))
        (terminalTime C L routes s ss a count (recordCount C.mesh (issued date)) reserve) ∧
      ∀i : Fin count,RouteSettlement.actual s.banks.used final i.val=
        (∑j,if site C.mesh (issued date) j=i then debit C.mesh (issued date) j else 0) ∧
        RouteSettlement.actual s.banks.reserved final i.val=reserve := by
  intro chk paid old routes out owners bits reserve final id amount paidReady
  have boot := StaticAt.issued C.mesh (issued date) (declaredRows C.mesh L) (issued_rows date) (L.arena.base C.mesh) cashBase publicROM
  let srcLayout := source S z W k attempts depth K₀ packed.groups H R
  have ae : A.first≤A.endAddress C.mesh := Nat.le_add_right ..
  have checkLow (i : ℕ) (hi : i<A.first) : chk i=initial i :=
    (ProtocolRAMGeneratedWrite.frame_image flag 1 (historyFlag C (events C.mesh)) _ i (.inl (hi.trans_le (ae.trans flagEnd)))).trans
      (run_frame C _ initial i mounted (fun e _=>floor _ _ (hi.trans_le (Nat.le_add_right ..))))
  have memoryLow (i : ℕ) (hi : i<A.first) : old i=initial i :=
    (L.before C.mesh count paid i (hi.trans_le (ae.trans (archRoom.cash.trans archRoom.owners)))).trans
      ((PaidWidths.frame _ _ _ _ _ i (fun b mem=>(paidReady b mem).1) (hi.trans_le (ae.trans archRoom.cash))).trans (checkLow i hi))
  have height : stop S z W k attempts depth K₀ packed.groups H R<2^w := stopEarly.trans_lt
    (lt_of_le_of_lt (ae.trans flagEnd) (by omega))
  have later := seen.frame height (fun i hi=>memoryLow _ (hi.trans_le stopEarly))
  have table : directoryBase S z W k attempts depth K₀ packed.groups H R≤ stop S z W k attempts depth K₀ packed.groups H R := Nat.le_add_right ..
  have readable := later.readable (table.trans height.le)
  have installed := boot.route.transfer A.first memoryLow recipeLow
  apply settle C A L (issued date) cashBase flag raw initial s src ss a pos countRoom reserveFits p srcLayout
    π place B order o physical ci cj sRoom archRoom routeInput flagEnd mounted floor
    (fun t=>issued_shape date t feedZero) spans args paidInputs amountSpan _ (issued_port date)
    flagFit flagBound widthBound rowBound safe space rowsFit menu kindCap indexCap ki end_ boot.sinkOwners
    ownerLow ownersBefore _ paidReady readable installed
  · intro t j
    rw [archRoom.zero,Nat.zero_add]
    exact issued_cash date t j
  · intro i hi
    have one := archRoom.kindOrder
    have two := archRoom.directory
    exact ⟨(checkLow _ (by omega)).trans (boot.kept i hi).1,(checkLow _ (by omega)).trans (boot.kept i hi).2⟩

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
