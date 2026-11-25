import OAI.Computability.BorderVNP.LabelIndexChooserSpace
import OAI.Computability.BorderVNP.CubeLabelPassFit
import OAI.Computability.BorderVNP.CubeLabelTraffic
import OAI.Computability.BorderVNP.CubeLabelISARealization

/-! # Fit of the complete label program on the indexed traffic table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA.LabelTrial MeanChoice

/-- At each trial the old cache and both incident subtotals are the scaled means for
the original traffic table. The pinned set and label map can vary with the cell. -/
def IndexedBinMeans (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m)
    (lab z : ℕ) (initial : ℕ → ℕ) : Prop :=
  ∀ (c : Fin l.cells) (v : Fin (z+1)),
    let p := l.trialFrame lab
    let rows := fun j => incidents (cableAt l m) j l.cableCount
    let t := p.prefix z rows initial c.val
    let b := p.bins c.val v.val t (rows c.val)
    let traffic := fromTables l m ep
    ∃ (s : Finset (Fin l.cells)) (x : Fin l.cells → Fin (z+1)),
      (∀ j, t (b.addr (binOrdinal z j).val) = cache traffic s x j) ∧
      (∀ j, b.before (binOrdinal z j).val = incidentSum traffic c s x j) ∧
      (∀ j, b.after (binOrdinal z j).val =
        incidentSum traffic c (insert c s) (Function.update x c v) j)

/-- All native cell and bin passes fit the allocated address space and selected word
width. The hypotheses bound only the public layout, raw volumes and mathematical means. -/
theorem indexed_frame_fitted {l : Layout} {m : ℕ → ℕ} {a : Acc}
    (view : View l m a l.cells l.cableCount l.deliveryCount (l.labels*l.labels) l.labels)
    (al : Allocated l) (ep : Endpoints l m) {lab w z : ℕ} (placement : LabelSegment l lab)
    (space : ChooserSpace l m lab w) (hz : l.labels = z+1)
    (count : l.labels^2+l.labels < 2^w)
    (cacheCap : totalWidth (fromTables l m ep)*(z+1)^2 < 2^w)
    (scoreCap : 2*(z+1)^6*(totalWidth (fromTables l m ep))^2 < 2^w)
    (model : IndexedBinMeans l m ep lab z a.mem) :
    (l.trialFrame lab).Fitted w z (fun j => incidents (cableAt l m) j l.cableCount) a.mem := by
  let p := l.trialFrame lab
  let rows j := incidents (cableAt l m) j l.cableCount
  have labels := space.labelAddr
  have sep : p.cables+p.Z^2 ≤ p.data := by simpa only [p,Layout.trialFrame,pow_two] using al.cableMean
  have both (c : Fin l.cells) (v : Fin (z+1)) (change : Bool) :
      PassRoom p w c.val v.val (p.prefix z rows a.mem c.val) (rows c.val) change := by
    have src (i : ℕ) (hi : i < p.Z^2+p.Z) :=
      indexed_pass_space view al ep placement space z c.val v.val i change
        (hz ▸ Nat.zero_lt_succ _) c.isLt hi
    refine ⟨fun i hi => (src i hi).1,fun i hi => (src i hi).2,?_⟩
    intro i hi
    let t := p.prefix z rows a.mem c.val
    let b := p.bins c.val v.val t (rows c.val)
    obtain ⟨s,x,means,old,new⟩ := model c v
    have small : i < (z+1)^2+(z+1) := by simpa only [p,Layout.trialFrame,hz] using hi
    cases change
    · exact trial_fits (fromTables l m ep) s x c v b t means new 0
        (by simpa only [Nat.zero_add] using scoreCap) i small
    · exact commit_fits (fromTables l m ep) s x c v b t means old new cacheCap i 0 small
        fun j hj eq => (Nat.ne_of_gt hj) (p.cacheAddr_injective sep eq)
  refine ⟨hz,count,fun c hc => ?_,fun _ hc _ hi => placement.off_cache al hc hi,?_,?_⟩
  · change lab+c < 2^w
    change c < l.cells at hc
    omega
  · intro c hc v
    exact both ⟨c,hc⟩ v false
  · intro c hc
    exact both ⟨c,hc⟩ (p.winner z c (p.prefix z rows a.mem c) (rows c)) true

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
