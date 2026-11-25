import OAI.Optimization.LinearProgramming.Compression.MinorOrder
import OAI.Optimization.LinearProgramming.Elimination.Basic
import OAI.Optimization.LinearProgramming.Compression.ProxyOracle
import OAI.Optimization.LinearProgramming.Compression.AdaptiveRequests

/-! The concrete determinant magnitudes, a proxy fixed independently of the order of requests,
and simultaneous clipping and restart bounds on all transcripts for two rational matrices. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

variable {rD rE N : ℕ} (D : Matrix (Fin rD) (Fin N) ℚ) (E : Matrix (Fin rE) (Fin N) ℚ)

/-- Evaluate just the supplied row and column selectors. The elimination routine tabulates each stage before moving to the next. -/
def evaluatePairMinor : PairMinorIndex rD rE N → ℚ
  | .inl ⟨_, row, col⟩ => Elimination.determinant (D.submatrix row col)
  | .inr ⟨_, row, col⟩ => Elimination.determinant (E.submatrix row col)

theorem evaluatePairMinor_eq (u : PairMinorIndex rD rE N) :
    evaluatePairMinor D E u = pairMinorValue D E u := by
  rcases u with ⟨_, row, col⟩ | ⟨_, row, col⟩ <;> exact Elimination.determinant_eq _

/-- Magnitude of a nonzero square minor, whether it was requested or not. -/
def minorMagnitude (u : NonzeroPairMinor D E) : ℚ := |evaluatePairMinor D E u.val|

theorem minorMagnitude_pos (u : NonzeroPairMinor D E) : 0 < minorMagnitude D E u := by
  simpa [minorMagnitude, evaluatePairMinor_eq] using abs_pos.mpr u.property

/-- True base-two logarithm (used only in the specification). -/
noncomputable def minorTrueLog (u : NonzeroPairMinor D E) : ℝ :=
  Real.logb 2 ((minorMagnitude D E u : ℚ) : ℝ)

/-- Fixed interpretation of the dyadic-or-symbolic rational proxy oracle. -/
noncomputable def minorProxy (fuel : ℕ) (u : NonzeroPairMinor D E) : ℝ :=
  let k := paperRadius N + 7
  let m := minorMagnitude D E u
  logProxyValue k m (logProxyNumerator fuel k m)

theorem minorProxy_close (fuel : ℕ) (u : NonzeroPairMinor D E) :
    |minorProxy D E fuel u - minorTrueLog D E u| ≤ 1/(paperGrid N : ℝ) := by
  have h := (logProxyValue_error fuel (paperRadius N+7) (minorMagnitude_pos D E u)).le
  apply h.trans
  rw [one_div_pow]
  have hpos : 0 ≤ 1 / (2:ℝ)^(paperRadius N+7) := by positivity
  simp only [paperGrid, Nat.cast_pow, Nat.cast_ofNat]
  linarith

/-- The online test never needs more than `paperWidth N` generator coordinates.
The preceding factor in the inequality is the sharper bound on actual restarts. -/
theorem minorProxy_independent_bound (fuel : ℕ) (hN : 1 ≤ N) (hr : rD+rE = N)
    (J : Finset (NonzeroPairMinor D E)) (hJ : IsDissociated (minorProxy D E fuel) J) :
    ((J.card : ℝ) ≤ (7*(N:ℝ)^2+8)*Real.logb 2 (N+1)) ∧ J.card ≤ paperWidth N := by
  have hclose (i : NonzeroPairMinor D E) :
      |minorProxy D E fuel i - Real.logb 2 (abs ((Rat.castHom ℝ) (pairMinorValue D E i.val)))| ≤
        1 / 2 ^ (100*(N+1)^3+7 : ℕ) := by
    have he := minorProxy_close D E fuel i
    have hv : minorTrueLog D E i = Real.logb 2 (abs ((Rat.castHom ℝ) (pairMinorValue D E i.val))) := by
      unfold minorTrueLog minorMagnitude
      rw [evaluatePairMinor_eq, Rat.cast_abs]
      rfl
    rw [hv] at he
    refine he.trans_eq ?_
    simp only [paperGrid, paperRadius, Nat.cast_pow, Nat.cast_ofNat]
  have h := dissociated_nonzeroPairMinor_card_le D E hN hr (Rat.castHom ℝ)
    Rat.cast_injective J (minorProxy D E fuel) (fun i _ => hclose i) hJ
  refine ⟨h, ?_⟩
  have hc := h.trans_lt (log_bound_lt_cutoff N)
  unfold paperWidth
  exact_mod_cast hc.le

/-- Every square minor of a matrix with no columns is the empty minor. -/
theorem minorMagnitude_zero_columns (D₀ : Matrix (Fin rD) (Fin 0) ℚ)
    (E₀ : Matrix (Fin rE) (Fin 0) ℚ) (u : NonzeroPairMinor D₀ E₀) :
    minorMagnitude D₀ E₀ u = 1 := by
  rcases u with ⟨u,hu⟩
  rcases u with ⟨⟨k,hk⟩,r,c⟩ | ⟨⟨k,hk⟩,r,c⟩
  all_goals
    have : k = 0 := by omega
    subst k
    simp only [minorMagnitude, evaluatePairMinor_eq, pairMinorValue, Matrix.det_isEmpty, abs_one]

/-- The zero-dimensional endpoint has no dissociated nonempty generator set. -/
theorem minorProxy_independent_bound_all (fuel : ℕ) (hr : rD+rE=N)
    (J : Finset (NonzeroPairMinor D E)) (hJ : IsDissociated (minorProxy D E fuel) J) :
    ((J.card : ℝ) ≤ (7*(N:ℝ)^2+8)*Real.logb 2 (N+1)) ∧ J.card ≤ paperWidth N := by
  cases N with
  | succ n => exact minorProxy_independent_bound D E fuel (Nat.succ_pos _) hr J hJ
  | zero =>
    have hgN : 0 < paperGrid 0 := Nat.two_pow_pos _
    have hg : (1 : ℝ) ≤ paperGrid 0 := by exact_mod_cast (show 1 ≤ paperGrid 0 from hgN)
    have small (j : NonzeroPairMinor D E) : |minorProxy D E fuel j| ≤ 1 := by
      have hlog : minorTrueLog D E j = 0 := by simp [minorTrueLog,minorMagnitude_zero_columns]
      have he := minorProxy_close D E fuel j
      rw [hlog,sub_zero] at he
      exact he.trans ((div_le_one (by positivity)).mpr hg)
    have hempty : J = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hh := hJ {j} (Finset.singleton_subset_iff.mpr hj) ∅ (Finset.empty_subset _) (by simp)
      have ht : 2 < |minorProxy D E fuel j| := by simpa using hh
      linarith [small j]
    simp [hempty]

/-- For every interactive prefix the answers since the latest restart extend to one
dimension-bounded rational assignment for the *actual* nonzero determinants. -/
theorem minor_transcript_guarantees_all (fuel : ℕ) (hr : rD+rE=N)
    (raw : ∀ J : Finset (NonzeroPairMinor D E),
      NonzeroPairMinor D E → Option ((Fin J.card → ℚ) × ℚ))
    (hraw : GoodRequestRows N (minorProxy D E fuel) raw)
    (commit : ∀ J : Finset (NonzeroPairMinor D E), J → ℚ)
    (hcommit : ∀ J, IsDissociated (minorProxy D E fuel) J →
      ValidEpochCommit (fun j : J => minorProxy D E fuel j) (paperWidth N)
        (epochHeightFor N J.card) (commit J))
    (hrestart : RestartTest (minorProxy D E fuel) (evaluateMinorRequest commit raw))
    (indices : List (NonzeroPairMinor D E)) :
    let st := RequestTrace.replay (evaluateMinorRequest commit raw) indices
    ((st.restarts : ℝ) ≤ (7*(N:ℝ)^2+8)*Real.logb 2 (N+1)) ∧
      ∃ f, ValidMinorAssignment N (minorTrueLog D E) f ∧
        ∀ u q, (u,q) ∈ st.replies → f u = q := by
  exact ⟨RequestTrace.restarts_le _ _ hrestart _
    (fun J hJ => (minorProxy_independent_bound_all D E fuel hr J hJ).1) indices,
    all_prefixes_extend N _ _ (minorProxy_close D E fuel)
      (fun J hJ => (minorProxy_independent_bound_all D E fuel hr J hJ).2)
      raw hraw commit hcommit hrestart indices⟩

/-- Positive-dimensional instance used in the LP reduction. -/
theorem minor_transcript_guarantees (fuel : ℕ) (_hN : 1 ≤ N) (hr : rD+rE=N)
    (raw : ∀ J : Finset (NonzeroPairMinor D E),
      NonzeroPairMinor D E → Option ((Fin J.card → ℚ) × ℚ))
    (hraw : GoodRequestRows N (minorProxy D E fuel) raw)
    (commit : ∀ J : Finset (NonzeroPairMinor D E), J → ℚ)
    (hcommit : ∀ J, IsDissociated (minorProxy D E fuel) J →
      ValidEpochCommit (fun j : J => minorProxy D E fuel j) (paperWidth N)
        (epochHeightFor N J.card) (commit J))
    (hrestart : RestartTest (minorProxy D E fuel) (evaluateMinorRequest commit raw))
    (indices : List (NonzeroPairMinor D E)) :
    let st := RequestTrace.replay (evaluateMinorRequest commit raw) indices
    ((st.restarts : ℝ) ≤ (7*(N:ℝ)^2+8)*Real.logb 2 (N+1)) ∧
      ∃ f, ValidMinorAssignment N (minorTrueLog D E) f ∧
        ∀ u q, (u,q) ∈ st.replies → f u = q := by
  exact minor_transcript_guarantees_all D E fuel hr raw hraw commit hcommit hrestart indices

end Compression
end LinearProgramming
end Optimization
end OAI
