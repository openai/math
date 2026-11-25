import OAI.Optimization.LinearProgramming.OracleSpec.NativePublic

/-! In dimension zero each true minor has zero logarithm. The general determinant request
service therefore cannot restart there, and the very same native transition serves every dimension. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace MinorLog

open OAI.Optimization.LinearProgramming.Compression

/-- All dimensions, using one native ordered-minor request policy, including uniformly at n=0. -/
theorem nativeHistory_correct_all {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ)
    (E : Matrix (Fin e) (Fin n) ℚ) (hrows : d+e=n) (us : List (Index D E)) :
    let exp := onlineMinorBitPolynomial.eval n
    let history := nativeHistory D E us
    history.map Prod.fst = us ∧ (∀ j, history.take j = nativeHistory D E (us.take j)) ∧
      restartCount history ≤ 15*n^2*((2*n).log2+1) ∧
      (∀ i q, (i,some q) ∈ history → RAM.ratBits q ≤ 3+2*exp) ∧
      (∀ j, extension n exp (logarithm D E) (history.take j)) := by
  cases n with
  | succ n => exact nativeHistory_correct D E (Nat.succ_pos _) hrows us
  | zero =>
    let _ := requestWordOrder D E
    let eqv := indexEquiv D E
    let fuel := manuscriptProxyFuel 0
    let proxy := fun u : Index D E => minorProxy D E fuel (eqv u)
    let req := nativePolicy D E
    have ht : RestartTest proxy req := (matrixMinorRequest_restartTest D E fuel).pullback eqv
    have hbound (J : Finset (Index D E)) (hJ : IsDissociated proxy J) : (J.card:ℝ) ≤ 0 := by
      have h := (minorProxy_independent_bound_all D E fuel hrows (J.map eqv.toEmbedding)
        ((isDissociated_map_iff (minorProxy D E fuel) eqv.toEmbedding J).mpr hJ)).1
      simpa using h
    have hnone : (RequestTrace.replay req us).restarts ≤ 0 := by
      exact_mod_cast RequestTrace.restarts_le proxy req ht 0 hbound us
    have he := serviceEvents_restartCount req RequestTrace.start us
    change (RequestTrace.replay req us).restarts = 0 + _ at he
    rw [zero_add] at he
    obtain ⟨size,ext⟩ := serviceEvents_pullback_contract eqv 0 (minorProxy D E fuel) (minorTrueLog D E)
      (matrixMinorRequest D E fuel) (matrixMinorRequest_restartTest D E fuel)
      (matrixMinorRequest_common_all D E fuel hrows) us
    have hlogs : (fun u : Index D E => minorTrueLog D E (eqv u)) = logarithm D E := by
      funext u
      simp [minorTrueLog,minorMagnitude,evaluatePairMinor_eq,eqv,indexEquiv_minor,logarithm]
    refine ⟨serviceEventsFrom_indices req _ us,fun j => serviceEventsFrom_take req _ us j,?_,size,?_⟩
    · change restartCount (serviceEventsFrom req RequestTrace.start us) ≤ _
      rw [← he]
      simpa using hnone
    · rw [← hlogs]
      exact ext

end MinorLog
end OracleSpec
end LinearProgramming
end Optimization
end OAI
