import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionInduction
import OAI.Optimization.LinearProgramming.PriceGame.TrialComparisons
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionChargeView
import OAI.Optimization.LinearProgramming.PriceGame.ChargingRecordedAllocation
import OAI.Optimization.LinearProgramming.PriceGame.Majority

/-! Failure of the executed trial implies the score charge on its selected experts, including
the root anchor. The only condition on the selected raw values is preservation of comparisons
at this trial's genuinely logged probes. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States States.Mass Charging Moment Finset

variable {N ne R : ℕ} {anchor : Fin N}

private def ChargesFailures (h : Hidden N R anchor) (experts : Fin ne → Expert N)
    (sel : Skeleton N → Fin ne) {r : ℕ} (fuel l : ℕ)
    (path : Path (Fin N) (Vertex N l)) (hist : History N) (out : Output N ne r l) : Prop :=
  ∀ (depth_eq : l + fuel = depth N), LoggedComparisons h experts sel out.log →
    ∀ s : FiniteState N l, Possible h hist path s → ¬s.wins h hist out.prices →
      1 ≤ weighted (stateWeight h s depth_eq.le sel) (fun e => (out.scores[e] : ℚ))

/-- Actual trial form of the charging lemma, with an arbitrary odd number of probes in
each group. The moment estimate later fixes the numerical branch count. -/
theorem execute_charge_odd (h : Hidden N R anchor) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (sel : Skeleton N → Fin ne)
    (roster : ∀ sk, sk.positive = h.positive → (experts (sel sk)).skeleton = sk)
    (k fuel l : ℕ) (path : Path (Fin N) (Vertex N l)) (hist : History N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (out : Certified (N:=N) (r:=2*k+1) (l:=l) w)
    (run : Computation.Reaches h (execute (2*k+1) R experts solve fuel l path hist w hw) out)
    (depth_eq : l + fuel = depth N) (keeps : LoggedComparisons h experts sel out.val.log)
    (s : FiniteState N l) (p : Possible h hist path s) (failure : ¬s.wins h hist out.val.prices) :
    1 ≤ weighted (stateWeight h s depth_eq.le sel) (fun e => (out.val.scores[e] : ℚ)) := by
  classical
  apply (execute_induct h experts solve (ChargesFailures h experts sel) ?_ ?_
    fuel l path hist w hw out run) depth_eq keeps s p failure
  · intro l path hist w bound _ s p failure
    have hl : l = depth N := by simpa using bound
    subst l
    exact (failure (by simpa only [leafOutput_prices] using p.leaf_wins)).elim
  · intro fuel l path hist w hw S steps ih eq keep s possible fail
    let child := nextCall (2*k+1) R experts solve fuel l path hist
    let lab := fun b : Calls k => (S.val (probeIndex b)).data.labels
    let parent := fun e : Fin ne => ((nodeScores experts S.val)[e] : ℚ)
    let cs := fun (b : Calls k ⊕ Calls k) (e : Fin ne) =>
      (callScore (S.val (groupedIndex (2*k+1) b)) e : ℚ)
    have lt : l < depth N := by omega
    have reached := (runSchedule_reaches_iff h _ _ _ _).mpr steps
    have gives (b : Calls k) :
        ∃ A : ProbeAllocation 64 (fun i : s.active => s.surplus h hist (chargeProbes S b) i),
        ∀ x : Fin 64 → s.active,
          probeGain A (fun i => if lab b i = h.positive then 1 else -1) x =
            callGain (S.val (probeIndex b)) (sel (localSkeleton h.positive s.pivot lt (fun j => x j))) := by
      obtain ⟨snap, rec, hsnap, _⟩ := reached_probe_receipt h experts solve w hw hist path child S reached b
      apply recorded_state_allocation h s lt sel rec hist hsnap roster
      exact keep _ (assemble_probe_mem_log experts hist w S b)
    choose alloc hgain using gives
    apply charge_state_node possible eq.le sel (chargeProbes S) (chargeChildren S) lab
      (fun b => reached_probe_feedback h experts solve w hw hist path child S b (steps _))
      alloc parent cs (fun b e => Nat.cast_nonneg _) ?_ ?_ ?_ ?_
    · intro x
      let sk := localSkeleton h.positive s.pivot lt (fun j => (x j : Vertex N l))
      have hl : mask experts l (sel sk) = true := by
        simp only [mask, Expert.isLocal, roster sk rfl]
        exact decide_eq_true rfl
      change ((nodeScores experts S.val)[sel sk] : ℚ) = _
      rw [nodeScores_local experts S.val _ hl, show chargeSigma = sigmaQ from paper_sigma_eq]
      apply congrArg (fun q : ℚ => (roundCharge sigmaQ q : ℚ))
      apply congrArg (weighted (uniform k))
      funext b
      exact (hgain b x).symm
    · intro a
      let sk := absoluteSkeleton h.positive s.pivot eq.le ⟨a.1.succ, a.2.1, a.2.2⟩
      have hd : mask experts l (sel sk) = false := by
        simp only [mask, Expert.isLocal, roster sk rfl, decide_eq_false_iff_not]
        change ¬ destination (a.1.val + 1) l = l
        rw [destination_eq]
        omega
      change ((nodeScores experts S.val)[sel sk] : ℚ) = _
      rw [nodeScores_deeper experts S.val _ hd, show chargeSigma = sigmaQ from paper_sigma_eq]
    · intro b o y stateNext hp hfail
      let j := groupedIndex (2*k+1) b
      have hi := ih j
      have he : (S.val j).data.baseline = callBaseline (chargeProbes S) b :=
        reached_callBaseline h experts solve w hw hist path child S steps b
      unfold ChargesFailures at hi
      rw [he] at hi
      have kc : LoggedComparisons h experts sel (S.val j).child.log := keep.mono
        (fun _ hp => assemble_child_log_subset experts hist w S j hp)
      exact hi (by omega) kc _ hp hfail
    · rwa [← reached_assembled_prices h experts solve w hw hist path child S steps]

/-- Root-specialized charge, on the same root weights in every trial with this selection. -/
theorem run_failure_charge (h : Hidden N R anchor) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (sel : Skeleton N → Fin ne)
    (roster : ∀ sk, sk.positive = h.positive → (experts (sel sk)).skeleton = sk)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (out : Certified (N:=N) (r:=probes) (l:=0) w)
    (reached : Computation.Reaches h (run R experts solve w hw) out)
    (keeps : LoggedComparisons h experts sel out.val.log)
    (failure : ¬(FiniteState.root h).wins h (fun _ _ => 0) out.val.prices) :
    1 ≤ weighted (rootWeight h sel) (fun e => (out.val.scores[e] : ℚ)) := by
  have gen (r : ℕ) (odd : Odd r) (out : Certified (N:=N) (r:=r) (l:=0) w)
      (reach : Computation.Reaches h (execute r R experts solve (depth N) 0 .root (fun _ _ => 0) w hw) out)
      (keep : LoggedComparisons h experts sel out.val.log)
      (fail : ¬(FiniteState.root h).wins h (fun _ _ => 0) out.val.prices) :
      1 ≤ weighted (rootWeight h sel) (fun e => (out.val.scores[e] : ℚ)) := by
    obtain ⟨k, rfl⟩ := odd
    exact execute_charge_odd h experts solve sel roster k (depth N) 0 .root (fun _ _ => 0)
      w hw out reach (by simp) keep (.root h) (.root _) fail
  exact gen probes probes_odd out reached keeps failure

/-- At an incorrect anchor vote the same fixed-weight charge applies. -/
theorem run_wrong_vote_charge (h : Hidden N R anchor) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (sel : Skeleton N → Fin ne)
    (roster : ∀ sk, sk.positive = h.positive → (experts (sel sk)).skeleton = sk)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (out : Certified (N:=N) (r:=probes) (l:=0) w)
    (reached : Computation.Reaches h (run R experts solve w hw) out)
    (keeps : LoggedComparisons h experts sel out.val.log)
    (wrong : decide (0 < out.val.prices anchor) ≠ h.positive) :
    1 ≤ weighted (rootWeight h sel) (fun e => (out.val.scores[e] : ℚ)) := by
  apply run_failure_charge h experts solve sel roster w hw out reached keeps
  intro wins
  apply wrong
  apply anchor_vote h out.val.prices
  intro i hi
  have b := wins i hi
  simpa [FiniteState.value, FiniteState.root, FiniteState.shift, FiniteState.decode,
    priority, rootVertex, signed, Hidden.signedPrice] using b

/-- This version fixes the weights by skeleton, making changes of the selected
identifier between different good intervals explicit. -/
theorem run_wrong_vote_skeleton_charge (h : Hidden N R anchor) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (sel : Skeleton N → Fin ne)
    (roster : ∀ sk, sk.positive = h.positive → (experts (sel sk)).skeleton = sk)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (out : Certified (N:=N) (r:=probes) (l:=0) w)
    (reached : Computation.Reaches h (run R experts solve w hw) out)
    (keeps : LoggedComparisons h experts sel out.val.log)
    (wrong : decide (0 < out.val.prices anchor) ≠ h.positive) :
    1 ≤ ∑ a, rootSkeletonWeight h a * (out.val.scores[sel
      (absoluteSkeleton h.positive none (by simp : 0 + depth N ≤ depth N) a)] : ℚ) := by
  have hb := run_wrong_vote_charge h experts solve sel roster w hw out reached keeps wrong
  unfold weighted at hb
  rwa [rootWeight_eq_skeleton_charge] at hb

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
