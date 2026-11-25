import OAI.Computability.BorderVNP.CubeISAOwnedStageFrame

/-! # One complete oriented singleton stage with its actual frame setup -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open VPVNP.BurstRAM DiagonalResidueRAM Cube.Scatter Owned Cube.Physical.Owned

/-- Addressed setup followed by the entire owned singleton pass. -/
def singleStage (n : ℕ) : Code := .seq OwnedRowSetup.single (rowLoop (singleCandidate n) scatterSingle)

/-- All private choices, memory and routed cursors of one oriented pass, as
returned from its actual scalar frame and current outer-loop control registers. -/
theorem singleStage_run {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : OwnedRowSetup.Layout) (D : SingleRowData n l.d (l.blocks*l.bc)) (src : Set ℕ)
    (r : Bank w) (m : Memory w) (entry : Entry D.axis D.left D.right r)
    (sel : r 36 = word w D.selector) (cross : r 37 = word w D.crossing)
    (loaded : l.Loaded n (readings pub) (readings m)) (fit : l.Fits w n (readings pub 0))
    (prepared : D.PreparedRow src m) (frameZ : (pub 0).val+56 ∈ src) (frameBank : (pub 0).val+88 ∈ src)
    (zAt : readings m ((pub 0).val+56) = l.d^(n+1)) (bankAt : readings m ((pub 0).val+88) = D.bank)
    (frameFit : (pub 0).val+88 < 2^w) (keys : l.d^(n+1)*l.d^(n+1) ≤ 2^w)
    (allocation : D.bank+l.d^(n+1)*l.d^(n+1)*(l.blocks*l.bc) < 2^w) :
    TraceRun pub mac (singleStage n) r m (rowChoices D.selected D.localBits)
      (OwnedRowSetup.single.slots +
        ((∑ t : Fin (singlePairTrials n l.d), (6*n+20+if D.selected t then startSingle.slots+5*(l.blocks*l.bc)+2 else 1))+1))
      (fun t mt => Keeps r t ∧ t 36 = word w D.selector ∧ t 37 = word w (D.before m (singlePairTrials n l.d)).1 ∧
        mt = (D.before m (singlePairTrials n l.d)).2) := by
  have first := traceRun_unsigned (OwnedRowSetup.single_run pub mac r m l D.axis D.left D.right
    loaded fit entry.zero entry.one entry.axis entry.left entry.right) (by decide)
  let post (t : Bank w) (mt : Memory w) := Keeps r t ∧ t 36 = word w D.selector ∧
    t 37 = word w (D.before m (singlePairTrials n l.d)).1 ∧ mt = (D.before m (singlePairTrials n l.d)).2
  have run := first.seq (Q := post) (fun u mu h => by
    obtain ⟨⟨r0,r1,r10,r11,r12,r14,r15,r18,r19⟩,_,r21,hold,hm⟩ := h
    have eqmem : mu = m := funext fun j => Fin.ext (congrFun hm j)
    subst mu
    have en : D.Entry u := ⟨r0,r1,r10,r11,r12,r14,r15,r18,r19,r21,
      (Fin.ext (hold 36 (by decide))).trans sel,(Fin.ext (hold 37 (by decide))).trans cross⟩
    apply (D.scatterRow_run pub mac src u m en prepared frameZ frameBank zAt bankAt frameFit keys allocation).mono le_rfl
    intro t mt h
    exact ⟨keeps_setup_loop hold h.low,h.selector,h.crossing,h.memory⟩)
  simpa only [singleStage,post,List.nil_append,show 6*n+17+3 = 6*n+20 by omega] using run

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
