import OAI.Hierarchy.ProtocolRAMCatalystDatedReads
import OAI.Hierarchy.ProtocolRAMCatalystLayoutTypes
import OAI.Hierarchy.ProtocolRAMCatalystOwnerLedger
import OAI.Hierarchy.ProtocolRAMReserveReconciliation
import OAI.Hierarchy.ProtocolRAMPaidWidthCore

namespace OAI
/-! # Native reserve reconciliation on the memory produced by the paid calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
variable {w q d count payload r edges : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {core : I→List (Fin edges)} {center : J→List (Fin edges)}

/-- Counters for inactive and padding rows are chosen by the same bounded expression
as the scan. Its value on active rows is the physical column/axis ordinal. -/
def nativeSite (L : OwnerLedger) (c : Mesh) (issued : Attempt→Entry count payload)
    (pos : 0<count) (m : Memory w) (j : Fin (recordCount c issued)) : Fin count :=
  let z := (rank c issued).symm j
  key pos ((L.term ((events c).get z.1)).eval m (z.2.val:Word w))

theorem native_debits (L : OwnerLedger) (c : Mesh) (issued : Attempt→Entry count payload)
    (pos : 0<count) (m : Memory w)
    (positive : ∀j,0<debit c issued j→nativeSite L c issued pos m j=site c issued j) (v : Fin count) :
    (∑j,if nativeSite L c issued pos m j=v then debit c issued j else 0)=
      ∑j,if site c issued j=v then debit c issued j else 0 := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hit : 0<debit c issued j
  · rw [positive j hit]
  · simp [Nat.eq_zero_of_not_pos hit]

theorem native_funded (L : OwnerLedger) (c : Mesh) (issued : Attempt→Entry count payload)
    (pos : 0<count) (m : Memory w)
    (positive : ∀j,0<debit c issued j→nativeSite L c issued pos m j=site c issued j) (v : Fin count) :
    (∑j,if nativeSite L c issued pos m j=v then debit c issued j else 0)≤fuel c*payload :=
  (native_debits L c issued pos m positive v).le.trans (funded c issued v)

omit [Fintype I] [Fintype J] in
/-- Before the scatter, both directory cells are still present, every owner was
written by the bounded native scan, and each amount is the actual word written by
its own dated commit. The lack of a positive debit permits a dummy owner. -/
theorem reconciliation (C : Chart w q d) (A : Arena) (L : OwnerLedger)
    (issued : Attempt→Entry count payload) (cashBase : Event→ℕ) (flag : ℕ)
    (routes : List Pass) (routeFloor : ℕ)
    (raw initial : Memory w) (s : Sink r edges) (src : ℕ) (ss : List PaidWidths.Slice)
    (a : ReserveUse.Archive) (pos : 0<count) (wcount : count<2^w) (enough : fuel C.mesh*payload<2^w)
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin count)
    (room : Room C.mesh A L a s.banks count (recordCount C.mesh issued) w)
    (routeInputs : (ReserveUse.word a s.banks).Fits w routeFloor)
    (routeLate : ∀p∈routes,routeFloor≤p.out)
    (high : A.endAddress C.mesh≤flag)
    (scheduled : mounted C (events C.mesh) initial)
    (floor : ∀ e x,x<A.base C.mesh e→protected C x e)
    (rows : ∀ t : Fin (events C.mesh).length,(atTime C.mesh issued t).rows=L.rows ((events C.mesh).get t))
    (span : ∀e∈events C.mesh,L.rows e≤L.arena.stride)
    (inputs : ∀e∈events C.mesh,(L.term e).Fits w s.banks.width.base)
    (amountSpan : ∀ t : Fin (events C.mesh).length,∀ j : Fin (atTime C.mesh issued t).rows,
      a.history.base+cashBase ((events C.mesh).get t)+j.val<A.base C.mesh ((events C.mesh).get t)+A.stride)
    (posted : ∀ t : Fin (events C.mesh).length,∀ j : Fin (atTime C.mesh issued t).rows,
      after C ((events C.mesh).get t) (run C ((events C.mesh).take t.val) initial)
        (a.history.base+cashBase ((events C.mesh).get t)+j.val)=((atTime C.mesh issued t).bits j:Word w)) :
    let checked := checkedOut C flag initial
    let paid := PaidWidths.output s.banks.width edges src ss checked
    let archived := result (L.scans C.mesh count) paid
    let id := sourceAt C.mesh issued (L.arena.base C.mesh)
    let amt := sourceAt C.mesh issued cashBase
    (∀u,u<2*recordCount C.mesh issued → checked (a.kind.base+u)=mount a id amt raw (a.kind.base+u) ∧
      checked (a.pointer.base+u)=mount a id amt raw (a.pointer.base+u)) →
    (∀p∈ss,p.Fits s.banks.width edges src w) →
    (∀j,0<debit C.mesh issued j→nativeSite L C.mesh issued pos checked j=site C.mesh issued j) →
    s.Before (result routes archived) enum ci (fun j=>(cj j).val) →
    Whole.Reconciliation s a (fuel C.mesh*payload) (nativeSite L C.mesh issued pos checked)
      (debit C.mesh issued) enum ci cj (result routes archived) := by
  intro checked paid archived id amt keep fits positive ports
  let n := recordCount C.mesh issued
  have dirEnd := room.directory
  have cashEnd := room.cash
  have start := room.owners
  have ownerEnd := room.archive
  have res := room.reserved
  have used := room.control
  have scratch := room.counters
  have end_ := room.end_
  have capacity : a.history.size<2^w := by omega
  have firstEnd : A.first≤A.endAddress C.mesh := Nat.le_add_right ..
  have old (x : ℕ) (hx : x < s.banks.width.base) : archived x=checked x :=
    (L.before C.mesh count paid x (hx.trans_le start)).trans (PaidWidths.frame _ _ _ _ _ x fits hx)
  have loaded := observed a s.banks id amt raw archived (nativeSite L C.mesh issued pos checked)
    (debit C.mesh issued) room.kindOrder room.kindSize room.ptrSize (by omega) (by
      intro u hu
      have h:=keep u hu
      have ko:=room.kindOrder
      exact ⟨(old _ (by omega)).trans h.1,(old _ (by omega)).trans h.2⟩) (by
      intro i
      let z := (rank C.mesh issued).symm i
      let e := (events C.mesh).get z.1
      have mem : e∈events C.mesh := List.get_mem ..
      let j := z.2.cast (rows z.1)
      have within := L.arena.within C.mesh e mem
      have rowLt : j.val<L.arena.stride := j.isLt.trans_le (span e mem)
      have iLt : id i<L.arena.endAddress C.mesh := (Nat.add_lt_add_left rowLt _).trans_le within
      refine ⟨iLt.trans_le ownerEnd,iLt.trans_le (ownerEnd.trans capacity.le),?_⟩
      rw [room.zero,Nat.zero_add]
      have hs := L.addressed C.mesh pos wcount paid span e mem
        (ProtocolRAMGeneratedWrite.fits_mono _ start (inputs _ mem)) j
      have same := eval_below (L.term e) (j.val:Word w) checked paid (inputs _ mem)
        (fun x hx=>PaidWidths.frame _ _ _ _ _ x fits hx)
      exact hs.trans (congrArg (fun z=>((key pos z).val:Word w)) same)) (by
      intro i
      let z := (rank C.mesh issued).symm i
      let e := (events C.mesh).get z.1
      have upper := (amountSpan z.1 z.2).trans_le (A.within C.mesh e (List.get_mem ..))
      have xlt : a.history.base+amt i<A.endAddress C.mesh := by simpa only [amt,sourceAt,Nat.add_assoc,z,e] using upper
      have other : L.arena.first≤L.arena.endAddress C.mesh := Nat.le_add_right ..
      refine ⟨by omega,by omega,(old _ (xlt.trans_le cashEnd)).trans ?_⟩
      exact checked_amount C A initial flag issued cashBase a.history scheduled floor amountSpan high posted i)
  have refs : (ReserveUse.word a s.banks).Fits w s.banks.reserved.base := by
    apply Expr.fits_of_inputEnd
    · simp only [ReserveUse.word,Expr.inputEnd,max_le_iff]
      have h := room.inputEnds
      omega
    · omega
  have readSame (i : Word w) := eval_below (ReserveUse.word a s.banks) i archived (result routes archived)
    routeInputs (fun x hx=>result_below _ _ _ (fun p hp=>hx.trans_le (routeLate p hp)))
  exact ⟨⟨room.control,room.counters,room.end_,refs,
    fun i=>⟨(readSame _).trans (loaded i).1,(readSame _).trans (loaded i).2⟩⟩,ports,room.usedSize,room.reservedSize,
    native_funded L C.mesh issued pos checked positive,enough⟩

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
