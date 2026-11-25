import OAI.Hierarchy.HistorySelectedDispatch

namespace OAI
/-! # Reconstructing all stage-dispatch operands from the published branch -/

namespace Hierarchy.HistorySelectedDispatch
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.TickWorkspace
open Diagonal.NavigationPass NativeNavigation Diagonal.HistoryContraction Diagonal.NavigationDirectory
open RAM RAM.NavigationNodeRows HistoryStageSetup HistoryPartyBatchExec
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {F Pins : Type} [Field F] [Fintype F] {u K heads heap fee levels : ℕ}
local notation "W" => 16*u^10
local notation "peak" => (2^((3*u^10+4)/5):ℕ)
variable (B : Block F) (cur ctr : Word (16*u^10)) (b : Banks) (mid issued warm : Memory (16*u^10))
    (headsAbove : base u 20≤heads) (heapBelow : heap≤base u 40)
    (unit : 0<b.unitWork) (peakFit : (2^((3*u^10+4)/5):ℕ)<2^(16*u^10))

include headsAbove heapBelow unit peakFit in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
omit [Fintype F] in
private theorem along {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (J : Run.WordSteps Pins r) (L : A.Words Pins) (C : r.Charges) (O : A.ArchiveSites)
    (p : r.ArchivePath h C O) (sums pairs : A.Site→ℕ) (paired : ∀x,L.ext x=2*pairs x)
    (charged : O.Charged b (numeric issued) sums pairs) (stored : r.ArchiveRowsStored b (numeric issued) h C O p)
    (ordered : A.OrderedHalves L) (initial : State.HalfRows O (halfArchiveCell u) (numeric mid))
    (program : r.WordVisits (RecordedWordStep K cur ctr heads heap mid Pins B.publicTemplate) h J L C O p)
    (directory : r.WordVisits (warmDirectoryVisit b warm) h J L C O p)
    (prices : r.WordVisits (Run.resourceVisit F Pins fee levels peak b (numeric issued)) h J L C O p) :
    r.WordVisits (stageRows B K heads heap fee levels cur ctr b mid issued warm) h J L C O p := by
  induction r with
  | done=>trivial
  | step R next ih=>
    let i:=h.1
    let step:=J.1 L i
    let mass:=fun v=>∑x : {x // R.parent i x=v},pairs x.val
    obtain ⟨cost⟩:=prices.1
    have small (v) : (R.next i).incidentWidth v<2^W := by
      have floor := cost.nextFloor v
      change 1+(R.next i).incidentWidth v ≤ R.push i (C.1 i) cost.prev v at floor
      exact (show (R.next i).incidentWidth v≤R.push i (C.1 i) cost.prev v by omega).trans_lt
        ((Nat.le_mul_of_pos_left _ unit).trans_lt ((cost.newCap v).trans_lt peakFit))
    have grown:=p.1.charged b (numeric issued) sums pairs charged stored.1
    have val (v) : step.words.ext v=2*mass v := by
      refine (step.ext_fiber v).trans ?_
      change (∑x : {x // R.parent i x=v},L.ext x.val)=2*∑x : {x // R.parent i x=v},pairs x.val
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _=>paired x.val
    have newer : State.HalfRows p.1.sites (halfArchiveCell u) (numeric mid) :=
      (program.1.halfRows small).transfer (fun _ _=>rfl) (fun _ a=>.inl ⟨headsAbove.trans a.1,a.2.trans_le heapBelow⟩)
    exact ⟨⟨program.1,directory.1,ordered,initial,newer,
      fun v=>(congrArg (2*·) (grown v).2).trans (val v).symm,⟨cost⟩⟩,
      ih i (Run.tailHistory R next h) (J.2 i) step.words (C.2 i) p.1.sites p.2
        (R.push i (C.1 i) sums) mass val grown stored.2.2 step.halves newer program.2 directory.2 prices.2⟩

include headsAbove heapBelow unit peakFit in
omit [Fintype F] in
theorem mounted_rows {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (J : Run.WordSteps Pins r) (L : A.Words Pins) (C : r.Charges) (O : A.ArchiveSites)
    (p : r.ArchivePath h C O) (first : LayerData O.layer)
    (mount : WarmSources u b (r.archiveList h C O p first) mid issued warm)
    (sums pairs : A.Site→ℕ) (paired : ∀x,L.ext x=2*pairs x)
    (charged : O.Charged b (numeric issued) sums pairs) (stored : r.ArchiveRowsStored b (numeric issued) h C O p)
    (ordered : A.OrderedHalves L) (initial : State.HalfRows O (halfArchiveCell u) (numeric mid))
    (program : r.WordVisits (RecordedWordStep K cur ctr heads heap mid Pins B.publicTemplate) h J L C O p)
    (prices : r.WordVisits (Run.resourceVisit F Pins fee levels peak b (numeric issued)) h J L C O p) :
    r.WordVisits (stageRows B K heads heap fee levels cur ctr b mid issued warm) h J L C O p :=
  along B cur ctr b mid issued warm headsAbove heapBelow unit peakFit r h J L C O p sums pairs paired
    charged stored ordered initial program (mount.directory_visits J L) prices

end
end Hierarchy.HistorySelectedDispatch

end OAI
