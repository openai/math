import OAI.Hierarchy.TraceReceiverSeedBudget
import OAI.Hierarchy.GridSelfHeader
import OAI.ThreeFlat.Diagonal.HistorySelectedChronology

namespace OAI
/-! # Exact S43 pair widths for the original physical receiver input -/

namespace Hierarchy.HistorySelectedPairWidths
open ThreeFlat Diagonal TraceDistribution Diagonal.TraceSourceOwner
open Diagonal.PhysicalStage RAM.NavigationNodeRows Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators

theorem raw_even (w e B n : ℕ) (ev : Even w) : Even (GridSelfHeader.rawSize w e B n) := by
  obtain ⟨h,rfl⟩ := ev
  refine ⟨e+2*h^2+B*(2*h^2)+(n+GridReceiverHeader.count (h+h))*(64*h),?_⟩
  unfold GridSelfHeader.rawSize
  ring

section Seed
variable {F : Type} [Field F] [Fintype F] {k low W pc regs words S base fuel : ℕ}
    (M : Machine W pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^W) (st : Word W)

theorem exact_seed (even : Even S) (v : PairedCursor.Site (k+1)) :
    TraceReceiverSeedWords.width M t hF st v=2*TraceReceiverSeedWords.pairs M t hF st v := by
  unfold TraceReceiverSeedWords.pairs
  by_cases active : v.1=0
  · simp only [TraceReceiverSeedWords.width,ite_eq_left active,bitIndex_pinCount,pinCount,pinSpan,
      Nat.one_mul,Nat.mul_one]
    rw [show (finFunctionFinEquiv v.2).val*(2*2^low)=2*((finFunctionFinEquiv v.2).val*2^low) by ring]
    obtain ⟨n,hn⟩ := even
    omega
  · simp [TraceReceiverSeedWords.width,active]
end Seed

section History
variable {F Pins : Type} [Field F]
open PhysicalStage.Run
def pairWordVisit (b : Banks) (mem : ℕ→ℕ) : WordVisit F Pins :=
  fun _ _ L step O _ row=>
    (∀x,2*archiveColumn b mem (O.id x) 1=L.ext x) ∧
    ∀v,2*archiveColumn b mem (row.sites.id v) 1=step.words.ext v

theorem pairWordVisits {d l : ℕ} {A : State d l} (r : Run F A)
    (h : r.plan.History) (J : WordSteps Pins r) (L : A.Words Pins) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (mem : ℕ→ℕ)
    (out : r.ArchiveRowsStored b mem h C O p) (start pairs : A.Site→ℕ)
    (paid : O.Charged b mem start pairs) (initial : ∀x,L.ext x=2*pairs x) :
    r.WordVisits (pairWordVisit b mem) h J L C O p := by
  induction r with
  | done=>trivial
  | step R next ih=>
    let j:=h.1
    let w:=J.1 L j
    let mass:=fun v=>∑ x : {x // R.parent j x=v},pairs x.val
    have grown:=p.1.charged b mem start pairs paid out.1
    have actual (v) : w.words.ext v=2*mass v:=by
      refine (w.ext_fiber v).trans ?_
      change (∑ x : {x // R.parent j x=v},L.ext x.val)=2*∑ x : {x // R.parent j x=v},pairs x.val
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _=>initial x.val
    refine ⟨⟨fun x=>?_,fun v=>?_⟩,ih j (tailHistory R next h) (J.2 j) w.words
      (C.2 j) p.1.sites p.2 out.2.2 (R.push j (C.1 j) start) mass grown actual⟩
    · exact (congrArg (2*·) (paid x).2).trans (initial x).symm
    · exact (congrArg (2*·) (grown v).2).trans (actual v).symm


end History
end Hierarchy.HistorySelectedPairWidths

end OAI
