import OAI.Hierarchy.ProtocolRAMCoreRouteSink
import OAI.Hierarchy.ProtocolRAMCoreRouteCost
import OAI.Hierarchy.ProtocolRAMCatalystStripLedger
import OAI.Hierarchy.ProtocolRAMCatalystArchiveCash

namespace OAI
/-! # Physical route publication and signed catalyst reconciliation on the same run -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard CatalystArchive
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
variable {z W k attempts w R K q d count payload edges : ℕ} {S : PurchaseSampler}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "r" => Fintype.card (Slots z D k)

/-- The two route passes, paid aggregation, signed owner emission, reserve scatter and final
reporter all use the very same memory. The per-event input is the real geometric port
certificate at the dated input and the cash word at the output of its commit. -/
theorem settle (C : Chart w q d) (A : Arena) (L : OwnerLedger) (issued : Attempt→Entry count payload)
    (cashBase : Event→ℕ) (flag : ℕ) (raw initial : Memory w) (s : Sink r edges) (src : ℕ)
    (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (pos : 0<count)
    (countRoom : count<2^w) (reserveFits : fuel C.mesh*payload<2^w)
    (p : Recipes) (x : Source) (π : Equiv.Perm (Fin (2^z))) (place : Site z D k→Fin K)
    (B : Mount (S:=S) π place edges) (order : Fin R≃Edges S z D k) (o : Orders z D k)
    (physical : ∀e,(B.row e).val=(order.symm e).val)
    (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→Fin count)
    (sRoom : SinkSpace s w) (archRoom : Room C.mesh A L a s.banks count (recordCount C.mesh issued) w)
    (routeInput : (ReserveUse.word a s.banks).Fits w s.banks.kind.base)
    (flagEnd : A.endAddress C.mesh≤flag) (mounted : Calendar.mounted C (events C.mesh) initial)
    (floor : ∀t u,u<A.base C.mesh t→protected C u t)
    (rows : ∀t : Fin (events C.mesh).length,(atTime C.mesh issued t).rows=L.rows ((events C.mesh).get t))
    (spans : ∀e∈events C.mesh,L.rows e≤L.arena.stride)
    (args : ∀t : Fin (events C.mesh).length,(L.term ((events C.mesh).get t)).Fits w (A.base C.mesh ((events C.mesh).get t)))
    (paidInputs : ∀e∈events C.mesh,(L.term e).Fits w s.banks.width.base)
    (amountSpan : ∀t : Fin (events C.mesh).length,∀j : Fin (atTime C.mesh issued t).rows,
      a.history.base+cashBase ((events C.mesh).get t)+j.val<A.base C.mesh ((events C.mesh).get t)+A.stride)
    (posted : ∀t : Fin (events C.mesh).length,∀j : Fin (atTime C.mesh issued t).rows,
      after C ((events C.mesh).get t) (run C ((events C.mesh).take t.val) initial)
        (a.history.base+cashBase ((events C.mesh).get t)+j.val)=((atTime C.mesh issued t).bits j:Word w))
    (dated : ∀t : Fin (events C.mesh).length,∀a,(events C.mesh).get t=.attempt a→
      PortROM (L.term (.attempt a)) (run C ((events C.mesh).take t.val) initial) (issued a))
    (flagFit : (historyFlag C (events C.mesh)).Fits w flag) (flagBound : flag+1<2^w)
    (widthBound : s.banks.width.base+edges<2^w)
    (rowBound : L.arena.endAddress C.mesh<2^w)
    (safe : Safe x S z W k attempts w s.banks.kind.base)
    (space : p.kind.Fits w s.banks.kind.base ∧ p.mode.Fits w s.banks.kind.base ∧ p.operand.Fits w s.banks.kind.base)
    (rowsFit : 2*r≤2^w) (menu : Fintype.card (Actions N k)≤2^w)
    (kindCap : 2*r≤ s.banks.kind.size) (indexCap : 2*r≤ s.banks.index.size)
    (ki : s.banks.kind.base+2*r≤ s.banks.index.base) (end_ : s.banks.index.base+2*r<2^w)
    (wordOwner : Owners s.owners edges initial)
    (ownerLow : s.owners.base+s.owners.size≤A.first) (ownersBefore : s.owners.base+s.owners.size≤ s.banks.kind.base) :
    let chk := checkedOut C flag initial
    let paid := PaidWidths.output s.banks.width edges src ss chk
    let old := result (L.scans C.mesh count) paid
    let routes := stages s.banks p x S z W k attempts
    let out := result routes old
    let owners := nativeSite L C.mesh issued pos chk
    let bits := debit C.mesh issued
    let reserve := fuel C.mesh*payload
    let final := ReserveUse.output a s.banks reserve owners bits out
    let id := sourceAt C.mesh issued (L.arena.base C.mesh)
    let amount := sourceAt C.mesh issued cashBase
    (∀u,u<2*recordCount C.mesh issued→chk (a.kind.base+u)=CatalystArchive.mount a id amount raw (a.kind.base+u) ∧
      chk (a.pointer.base+u)=CatalystArchive.mount a id amount raw (a.pointer.base+u)) →
    PaidWidths.Mounted s.banks.width edges src ss chk →
    Readable x S z W k attempts order π old → Installed p o ci (fun i=>(cj i).val) old →
    Whole.Reconciliation s a reserve owners bits (enum B o) ci cj out ∧
      (terminal C L routes flag s src ss a count (recordCount C.mesh issued) reserve).Exec initial
        (s.output final (enum B o) ci (fun i=>(cj i).val))
        (terminalTime C L routes s ss a count (recordCount C.mesh issued) reserve) ∧
      ∀i : Fin count,RouteSettlement.actual s.banks.used final i.val=
        (∑j,if site C.mesh issued j=i then debit C.mesh issued j else 0) ∧
        RouteSettlement.actual s.banks.reserved final i.val=reserve := by
  intro chk paid old routes out owners bits reserve final id amount kept paidReady native recipes
  have ae : A.first≤A.endAddress C.mesh := Nat.le_add_right ..
  have copies := sRoom.wide
  have guard : 2<2^w := by exact lt_of_lt_of_le (by decide : 2<2^3) (Nat.pow_le_pow_right (by decide) copies.le)
  have positive := nativeSite_from_portROM C A initial flag L issued pos countRoom mounted floor args (fun t=>
    (Nat.le_add_right (A.base C.mesh _) A.stride).trans ((A.within C.mesh _ (List.get_mem ..)).trans flagEnd)) dated
  have fit := fun t ht=>(paidReady t ht).1
  have owns := owners_at_route C A L flag count s src ss initial wordOwner mounted floor ownerLow
    (ae.trans flagEnd) (ae.trans archRoom.cash) archRoom.owners fit
  have setup := before p x s π place B order o physical old native ci (fun i=>(cj i).val) recipes owns
    sRoom rowsFit guard menu kindCap indexCap ki ownersBefore (index_fits p x safe space)
  have bootstrapped := reconciliation C A L issued cashBase flag routes s.banks.kind.base raw initial s src ss a
    pos countRoom reserveFits (enum B o) ci cj archRoom routeInput (by
      intro t member
      simp only [routes,stages,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl
      · exact le_rfl
      · exact Nat.le_trans (Nat.le_add_right ..) ki) flagEnd mounted floor rows spans paidInputs amountSpan posted
    kept fit positive setup
  refine ⟨bootstrapped,terminal_exec C L routes flag s src ss a issued pos (pass_fits p x s.banks safe space ki end_)
    (enum B o) ci cj initial mounted flagFit flagBound widthBound spans (fun e he=>
      ProtocolRAMGeneratedWrite.fits_mono _ archRoom.owners (paidInputs _ he)) rowBound paidReady bootstrapped,?_⟩
  intro i
  obtain ⟨used,full⟩ := ReserveUse.reported a s.banks reserve owners bits out bootstrapped.archive i
    bootstrapped.usedSize bootstrapped.reserveSize (bootstrapped.funded i) reserveFits
  exact ⟨used.trans (native_debits L C.mesh issued pos chk positive i),full⟩

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
