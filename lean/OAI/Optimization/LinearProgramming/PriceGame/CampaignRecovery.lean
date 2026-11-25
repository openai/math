import OAI.Optimization.LinearProgramming.PriceGame.CampaignRounds
import OAI.Optimization.LinearProgramming.PriceGame.Campaign
import OAI.Optimization.LinearProgramming.PriceGame.PhasesIds
import OAI.Optimization.LinearProgramming.PriceGame.LearningPolynomial
import OAI.Optimization.LinearProgramming.PriceGame.ChargingSkeleton

/-! Assemble the greedy exception partition, the executed trial weights and the root charges.
Every operation on the hidden costs in this file is used solely to analyze the public campaign. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Campaign

open Finset States.Mass Learning Charging

set_option exponentiation.threshold 300 in
theorem rounds_eq_source_exponent (N R : ℕ) :
    rounds N R = (inputSize N R)^(Pool.exceptionExponent + 1 + 74) :=
  (rounds_eq N R).trans (congrArg (fun k : ℕ => (inputSize N R)^k)
    (show 300 = Pool.exceptionExponent + 1 + 74 by rfl))


abbrev RootSkeleton (N : ℕ) := SelectedSkeleton (Vertex N 0) 64 (depth N)

def rootSkeleton {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor) (a : RootSkeleton N) : Skeleton N :=
  absoluteSkeleton h.positive none (by simp : 0 + depth N ≤ depth N) a

/-- The two per-trial facts used in the Section 7 reduction. The first is a cost of the
actual output. The second tests the selected experts against that output's recorded comparisons. -/
structure RoundGuarantees {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (markets : AvailableMarkets N) : Prop where
  log_bound (p : Population N) (result : RoundResult N)
    (reached : Computation.Reaches h (runRound R markets p) result) :
    result.observations.length ≤ Pool.probeBudget N
  charge (p : Population N) (result : RoundResult N)
    (reached : Computation.Reaches h (runRound R markets p) result)
    (sel : Skeleton N → Fin p.experts.length)
    (roster : ∀ sk, sk.positive = h.positive → (populationExperts p (sel sk)).skeleton = sk)
    (comparisons : ∀ sk, sk.positive = h.positive →
      ∀ q ∈ result.observations.flatMap sk.testsAt,
        compare (featureValue (populationExperts p (sel sk)).raw q.feature) q.threshold =
        compare (featureValue (States.priority h) q.feature) q.threshold)
    (miss : failedTrial h result = true) :
    1 ≤ ∑ a : RootSkeleton N, rootSkeletonWeight h a *
      (result.scores (sel (rootSkeleton h a)) : ℚ)

private theorem real_truth {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (out : ℕ → RoundResult N) (i : Fin N) :
    (((Phases.Trace.fromHidden h out).truth i : ℤ) : ℚ) = States.priority h i := by
  simp [Phases.Trace.fromHidden, States.priority]

theorem seenProbes_bound {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (markets : AvailableMarkets N) (g : RoundGuarantees h markets) (out : ℕ → RoundResult N) {T : ℕ}
    (hr : ValidRun (Pool.batch N R) (runRound R markets) h T
      (Population.start (Pool.batch N R)) (fun i => out i.val)) (t : ℕ) (ht : t ≤ T) :
    (seenProbes out t).length ≤ t * Pool.probeBudget N := by
  induction t with
  | zero => simp [seenProbes]
  | succ t ih =>
    have step := (validRun_iff_steps ..).mp hr t (by omega)
    simpa [seenProbes, Nat.succ_mul] using Nat.add_le_add (ih (by omega)) (g.log_bound _ _ step)

private theorem size_facts {N R : ℕ} (anchor : Fin N) :
    2 ≤ inputSize N R ∧ N ≤ inputSize N R ∧ R.size ≤ inputSize N R := by
  have hN := anchor.isLt
  simp only [inputSize]
  omega

theorem current_pool_le {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (markets : AvailableMarkets N) (g : RoundGuarantees h markets) (out : ℕ → RoundResult N) {T : ℕ}
    (hr : ValidRun (Pool.batch N R) (runRound R markets) h T
      (Population.start (Pool.batch N R)) (fun i => out i.val)) (t : ℕ) (ht : t < T) :
    (population R out t).ids.card ≤ (inputSize N R * T)^Pool.catalogueExponent := by
  rw [Population.ids, card_range, population_entries]
  apply (Catalog.length_mono (fun u => Pool.batch N R (seenProbes out u)) ht).trans
  obtain ⟨hX,hN,_⟩ := size_facts (R:=R) anchor
  apply Pool.catalogue_size_power N R _ _ (Nat.zero_lt_of_lt anchor.isLt) hN hX (Nat.zero_lt_of_lt ht)
  intro j hj
  exact (seenProbes_bound h markets g out hr j hj.le).trans (Nat.mul_le_mul_right _ hj.le)

theorem good_segment_bound {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (hR : 0 < R) (markets : AvailableMarkets N) (g : RoundGuarantees h markets)
    (out : ℕ → RoundResult N) {T : ℕ}
    (hr : ValidRun (Pool.batch N R) (runRound R markets) h T
      (Population.start (Pool.batch N R)) (fun i => out i.val))
    (b : Fin (Phases.Trace.budget N R+1))
    (seg : Phases.Segment (Phases.Trace.fromHidden h out).miss
      ((Phases.Trace.fromHidden h out).exception_count T hR (Phases.Trace.fromHidden_box h out)) b) :
    ∑ j ∈ range seg.length, (if failedTrial h (out (seg.first.val+j)) then (1 : ℝ) else 0) ≤
      (1/8 : ℝ) * seg.length + Real.logb 2 (64 * (((inputSize N R * T)^Pool.catalogueExponent : ℕ) : ℝ)) := by
  classical
  let history := Phases.Trace.fromHidden h out
  let hP := Phases.Trace.fromHidden_box h out
  let ix : Skeleton N → ℕ := history.expertId hP seg.first
  let selected (a : RootSkeleton N) := ix (rootSkeleton h a)
  apply charged_segment_bound h markets out T seg.first.val seg.length _ hr seg.finish_le
    (current_pool_le h markets g out hr _ seg.first.isLt) selected
    (fun a => history.expertId_mem hP (t:=seg.first.val) (Nat.le_refl _) (rootSkeleton h a))
    (rootSkeletonWeight h) (rootSkeletonWeight_nonneg h) (sum_rootSkeletonWeight_le_one h)
  intro j hj hmiss
  let t := seg.first.val+j
  let p := population R out t
  have hle : seg.first.val ≤ t := Nat.le_add_right ..
  let sel (s : Skeleton N) : Fin p.experts.length :=
    ⟨ix s, mem_range.mp (history.expertId_mem hP hle s)⟩
  have he (s : Skeleton N) : populationExperts p (sel s) = history.chosen seg.first s := by
    have hl := history.expertId_lookup hP hle s
    obtain ⟨_, helem⟩ := List.getElem?_eq_some_iff.mp hl
    exact helem
  have hs (s : Skeleton N) (_ : s.positive = h.positive) :
      (populationExperts p (sel s)).skeleton = s := congrArg Expert.skeleton (he s)
  have hc (s : Skeleton N) (hp : s.positive = h.positive) (q : Test N)
      (hq : q ∈ (out t).observations.flatMap s.testsAt) :
      compare (featureValue (populationExperts p (sel s)).raw q.feature) q.threshold =
      compare (featureValue (States.priority h) q.feature) q.threshold := by
    rw [he]
    have z := ((history.segment_selection hP hR seg s hp).2 j hj).2 q hq
    simpa only [history, real_truth h out] using z
  have hreached := (validRun_iff_steps ..).mp hr t (by dsimp [t]; have := seg.finish_le; omega)
  exact g.charge p (out t) hreached sel hs hc hmiss

private theorem validRun_ext {N R : ℕ} {anchor : Fin N} {T : ℕ}
    (h : Hidden N R anchor) (p : Population N) (markets : AvailableMarkets N)
    {a b : Fin T → RoundResult N} (eq : a = b)
    (valid : ValidRun (Pool.batch N R) (runRound R markets) h T p b) :
    ValidRun (Pool.batch N R) (runRound R markets) h T p a := by
  rw [eq]
  exact valid

private theorem strategy_correct_from_traces {N R : ℕ} {anchor : Fin N}
    (h : Hidden N R anchor) (markets : AvailableMarkets N) (T : ℕ)
    (post : ∀ out : ℕ → RoundResult N,
      ValidRun (Pool.batch N R) (runRound R markets) h T
        (Population.start (Pool.batch N R)) (fun i => out i.val) →
      priceMajority (fun i : Fin T => (out i.val).prices anchor) = h.positive) :
    Tree.Correct h (strategy R T anchor markets) := by
  apply trialStrategy_correct_of_runs
  intro results hrun
  let out : ℕ → RoundResult N := fun i =>
    if hh : i < T then results ⟨i,hh⟩ else ⟨fun _ => 0, fun _ => 0, []⟩
  have hout (i : Fin T) : out i.val = results i := by simp [out,i.isLt]
  have same : (fun i : Fin T => out i.val) = results := funext hout
  have hr := validRun_ext h (Population.start (Pool.batch N R)) markets same hrun
  simpa only [hout] using post out hr

private theorem vote_at_time {X e c j E m N R T : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (htime : T = X ^ (e + 1 + j)) (hX : 2 ≤ X) (hm : 1 ≤ m)
    (hE : E ≤ X ^ e) (hmSize : m ≤ (X * T)^c)
    (hexp : 4 * (13 + 2*c*(e+1+j+1)) < 2^j)
    (x : Fin T → Fin N → ℚ) (failed : Finset (Fin T)) (tag : Fin T → Option (Fin (E+1)))
    (hexc : (univ.filter fun t => tag t = none).card ≤ E)
    (hsuccess : ∀ t ∉ failed, ∀ i ∈ h.active, (R+1:ℚ) - (h.cost i : ℕ) ≤ h.signedPrice (x t i))
    (hblock : ∀ b : Fin (E+1),
      ∑ t ∈ univ.filter (fun t => tag t = some b), (if t ∈ failed then (1 : ℝ) else 0) ≤
      (1/8:ℝ) * (univ.filter (fun t => tag t = some b)).card + Real.logb 2 (64 * (m:ℝ))) :
    priceMajority (fun i => x i anchor) = h.positive := by
  subst T
  exact polynomial_trials_vote h hX hm hE hmSize hexp x failed tag hexc hsuccess hblock

/-- Section 7 applied to the exact public recursive algorithm and its adaptive experts. -/
theorem correct_of_roundGuarantees {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (hR : 0 < R) (markets : AvailableMarkets N) (g : RoundGuarantees h markets) :
    Tree.Correct h (strategy R (rounds N R) anchor markets) := by
  generalize htime : rounds N R = T
  apply strategy_correct_from_traces h markets T
  intro out hr
  let X := inputSize N R
  let M := (X*T)^Pool.catalogueExponent
  let r := Phases.Trace.fromHidden h out
  let hP := Phases.Trace.fromHidden_box h out
  let E := Phases.Trace.budget N r.R
  have exc : (Phases.events r.miss T).card ≤ E := r.exception_count T hR hP
  let tag := Phases.tag r.miss T E exc
  let failed : Finset (Fin T) := univ.filter fun t => failedTrial h (out t)
  have hX := (size_facts (R:=R) anchor).1
  have hXpos : 0 < X := Nat.lt_of_lt_of_le (by decide : 0 < 2) hX
  have htx := htime.symm.trans (rounds_eq_source_exponent N R)
  have hTpos : 0 < T :=
    (Nat.mul_pos (Nat.pow_pos hXpos (n:=150)) (Nat.pow_pos hXpos (n:=150))).trans_eq htime
  have hm : 1 ≤ M := Nat.one_le_pow _ _ (Nat.mul_pos hXpos hTpos)
  have hE := Pool.exception_size_power N R X (Nat.zero_lt_of_lt anchor.isLt)
    (size_facts (R:=R) anchor).2.1 (size_facts (R:=R) anchor).2.2 hX
  have hB : ∀ b : Fin (E+1),
      ∑ t ∈ univ.filter (fun t => tag t = some b), (if t ∈ failed then (1:ℝ) else 0) ≤
      (1/8 : ℝ) * (univ.filter (fun t => tag t = some b)).card + Real.logb 2 (64 * (M:ℝ)) := by
    intro b
    let F := fun t : ℕ => if failedTrial h (out t) then (1 : ℝ) else 0
    have hf : ∀ t : Fin T, (if t ∈ failed then (1 : ℝ) else 0) = F t.val := by simp [failed,F]
    simp_rw [hf]
    let s := univ.filter fun t : Fin T => tag t = some b
    by_cases hs : s.Nonempty
    · let seg := Phases.segment (T:=T) (E:=E) r.miss exc b hs
      have hcard : s.card = seg.length := seg.card_eq
      have hsum : (∑ t ∈ s, F t.val) = ∑ j ∈ range seg.length, F (seg.first.val+j) := seg.sum_eq F
      change (∑ t ∈ s, F t.val) ≤ (1/8:ℝ)*s.card + _
      rw [hsum,hcard]
      exact good_segment_bound h hR markets g out hr b seg
    · have empty := Finset.not_nonempty_iff_eq_empty.mp hs
      change (∑ t ∈ s, F t.val) ≤ (1/8 : ℝ)*s.card + _
      rw [empty]
      simp only [sum_empty, card_empty, Nat.cast_zero, mul_zero, zero_add]
      apply Real.logb_nonneg (by norm_num)
      exact_mod_cast (show 1 ≤ 64 * M by omega)
  have main := vote_at_time (X:=X) (e:=Pool.exceptionExponent) (c:=Pool.catalogueExponent)
    (j:=74) (E:=E) (m:=M) h htx hX hm hE le_rfl Pool.trial_exponent_adequate
    (fun i => (out i.val).prices) failed tag
    ((Phases.exceptional_fiber exc).trans_le exc) (fun t ht => succeeds_of_not_failed h _ (by simpa [failed] using ht)) hB
  exact main

end Campaign
end PriceGame
end LinearProgramming
end Optimization
end OAI
