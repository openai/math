import OAI.Optimization.LinearProgramming.Compression.Epoch
import OAI.Optimization.LinearProgramming.Compression.RequestFamily
import OAI.Optimization.LinearProgramming.Compression.Restart

/-! Online minor compression across arbitrarily many adaptive requests and restarts. The
local request interface is discharged by the lattice request lemma; the numerical bound
and simultaneous-extension conclusion here hold for every transcript. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

def paperRadius (N : ℕ) : ℕ := 100*(N+1)^3
def paperGrid (N : ℕ) : ℕ := 2^(paperRadius N+7)
def paperWidth (N : ℕ) : ℕ := (N+1)^6

def epochCandidateHeight (N k : ℕ) : ℕ := requestCutoff (k+1)*paperGrid N

def epochHeightFor (N k : ℕ) : ℕ :=
  epochRowHeight (paperRadius N) (paperGrid N) (max (epochCandidateHeight N k) (2*paperGrid N))

/-- Size and four-term comparison clauses for a complete assignment of the logarithms. -/
def ValidMinorAssignment (N : ℕ) (trueLog : ι → ℝ) (f : ι → ℚ) : Prop :=
  (∀ u, |f u| ≤ ((2:ℕ)^(onlineMinorBitPolynomial.eval N) : ℕ) ∧
    (f u).num.natAbs ≤ 2^(onlineMinorBitPolynomial.eval N) ∧
    (f u).den ≤ 2^(onlineMinorBitPolynomial.eval N)) ∧
  ∀ a : ι → ℤ, (∑ u, |(a u : ℝ)|) ≤ 4 →
    |clip (paperRadius N) (intForm a (fun u => (f u : ℝ))) -
      clip (paperRadius N) (intForm a trueLog)| ≤ 1/(2:ℝ)^(paperRadius N)

private def liftUniv (i : ι) : (Finset.univ : Finset ι) := ⟨i,Finset.mem_univ i⟩

omit [LinearOrder ι] in
private theorem reindex_sum (f : ↥(Finset.univ : Finset ι) → ℝ) :
    (∑ u, f u) = ∑ i : ι, f (liftUniv i) := by
  exact Finset.univ.sum_coe_sort (fun i => f (liftUniv i))

/-- A local successful representation needs only approximate the proxy logarithm, and be
small. Its coefficients were selected before seeing any committed rational generator values. -/
structure GoodRequestRows (N : ℕ) (proxy : ι → ℝ)
    (raw : ∀ J : Finset ι, ι → Option ((Fin J.card → ℚ) × ℚ)) : Prop where
  spec : ∀ J : Finset ι, IsDissociated proxy J →
    let F := knownRequestFamily (Finset.univ : Finset ι) J (raw J)
    let H := epochCandidateHeight N J.card
    ∀ u ∈ acceptedRequests Finset.univ J (raw J),
      |F.eval (fun j => proxy j) u - proxy u| ≤ 1 / (paperGrid N : ℝ) ∧
      (∀ j, (F.coefficient u j).num.natAbs ≤ H ∧ (F.coefficient u j).den ≤ H) ∧
      (F.offset u).num.natAbs ≤ H ∧ (F.offset u).den ≤ H

/-- A generator set determines a single complete assignment valid even for successful
requests that have not yet been issued. -/
theorem all_successful_requests_extend (N : ℕ) (proxy trueLog : ι → ℝ)
    (hproxy : ∀ i, |proxy i - trueLog i| ≤ 1/(paperGrid N : ℝ))
    (hwidth : ∀ J : Finset ι, IsDissociated proxy J → J.card ≤ paperWidth N)
    (raw : ∀ J : Finset ι, ι → Option ((Fin J.card → ℚ) × ℚ))
    (hrows : GoodRequestRows N proxy raw)
    (commit : ∀ J : Finset ι, J → ℚ)
    (hcommit : ∀ J : Finset ι, IsDissociated proxy J →
      ValidEpochCommit (fun j : J => proxy j) (paperWidth N)
        (epochHeightFor N J.card) (commit J))
    (J : Finset ι) (hJ : IsDissociated proxy J) :
    ∃ f : ι → ℚ, ValidMinorAssignment N trueLog f ∧
      ∀ u q, evaluateMinorRequest commit raw J u = some q → f u = q := by
  classical
  let U := (Finset.univ : Finset ι)
  let F := knownRequestFamily U J (raw J)
  let S := acceptedRequests U J (raw J)
  have hE : 0 < paperGrid N := by dsimp [paperGrid]; positivity
  have hgood := hrows.spec J hJ
  obtain ⟨f, hagree, hsize, hclip⟩ := epoch_commit_extends_accepted proxy U J
    (fun u => trueLog u) (Finset.subset_univ _) hJ (paperWidth N) (paperRadius N)
    (paperGrid N) (epochCandidateHeight N J.card) hE (fun I _ => hwidth I)
    (fun u => hproxy u) S F (fun u hu => (hgood u hu).1)
    (fun u hu => (hgood u hu).2.1) (fun u hu => (hgood u hu).2.2) (commit J) (hcommit J hJ)
  refine ⟨fun i => f (liftUniv i), ⟨?_, ?_⟩, ?_⟩
  · intro i
    have hcap := fiber_manuscript_value_height N J.card (paperWidth N) (hwidth J hJ) le_rfl
    have hn := (hsize (liftUniv i)).1.trans hcap
    have hd := (hsize (liftUniv i)).2.trans hcap
    exact ⟨(rat_abs_le_num_natAbs _).trans (by exact_mod_cast hn), hn, hd⟩
  · intro a ha
    have hm : (∑ u : U, |(a u.val : ℝ)|) ≤ 4 := by
      rw [reindex_sum]
      exact ha
    have h := hclip (fun u => a u.val) hm
    unfold intForm at h ⊢
    rw [reindex_sum, reindex_sum] at h
    apply h.trans
    simpa only [paperGrid, Nat.cast_pow, Nat.cast_ofNat] using seventeen_units_le_clip_precision (paperRadius N)
  · intro i q hh
    have ha := mem_accepted_of_evaluate_some U J raw commit (liftUniv i) hh
    have h := knownRequestFamily_evaluate U J raw commit (liftUniv i) ha
    exact (hagree _ ha).trans (Option.some.inj (h.symm.trans hh))

/-- Every adaptively selected prefix inherits the same per-epoch guarantee. -/
theorem all_prefixes_extend (N : ℕ) (proxy trueLog : ι → ℝ)
    (hproxy : ∀ i, |proxy i - trueLog i| ≤ 1/(paperGrid N : ℝ))
    (hwidth : ∀ J : Finset ι, IsDissociated proxy J → J.card ≤ paperWidth N)
    (raw : ∀ J : Finset ι, ι → Option ((Fin J.card → ℚ) × ℚ))
    (hrows : GoodRequestRows N proxy raw)
    (commit : ∀ J : Finset ι, J → ℚ)
    (hcommit : ∀ J : Finset ι, IsDissociated proxy J →
      ValidEpochCommit (fun j : J => proxy j) (paperWidth N)
        (epochHeightFor N J.card) (commit J))
    (hrestart : RestartTest proxy (evaluateMinorRequest commit raw)) (indices : List ι) :
    ∃ f : ι → ℚ, ValidMinorAssignment N trueLog f ∧
      ∀ u q, (u,q) ∈ (RequestTrace.replay (evaluateMinorRequest commit raw) indices).replies →
        f u = q := by
  apply RequestTrace.common_assignment proxy _ hrestart
  exact all_successful_requests_extend N proxy trueLog hproxy hwidth raw hrows commit hcommit

/-- A single rational commitment of generator coordinates exists before each run's requests;
its sign guarantees suffice for every possible completion. -/
noncomputable def canonicalMinorCommit (N : ℕ) (proxy : ι → ℝ) (J : Finset ι) : J → ℚ :=
  epochCommit (fun j : J => proxy j) (paperWidth N) (epochHeightFor N J.card)

omit [LinearOrder ι] [Fintype ι] in
theorem canonicalMinorCommit_valid (N : ℕ) (proxy : ι → ℝ) (J : Finset ι) :
    ValidEpochCommit (fun j : J => proxy j) (paperWidth N) (epochHeightFor N J.card)
      (canonicalMinorCommit N proxy J) := epochCommit_valid ..

end Compression
end LinearProgramming
end Optimization
end OAI
