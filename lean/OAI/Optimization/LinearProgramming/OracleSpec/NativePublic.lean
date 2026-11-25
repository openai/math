import OAI.Optimization.LinearProgramming.Compression.MinorNative
import OAI.Optimization.LinearProgramming.Compression.ProxyFuel
import OAI.Optimization.LinearProgramming.OracleSpec.Companion
import OAI.Optimization.LinearProgramming.Compression.PublicPolicy
import OAI.Optimization.LinearProgramming.Compression.ServiceBound
import OAI.Optimization.LinearProgramming.OracleSpec.IndexOrder
import OAI.Optimization.LinearProgramming.OracleSpec.UnitService

/-! On-demand minor response correctness on the exact public request type. The service below
executes the two native lattice reductions and uses the dimension-only proxy cutoff. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace MinorLog

open OAI.Optimization.LinearProgramming.Compression
open scoped BigOperators

variable {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)

/-- The native procedure on the public requests. Only its current generators and the
requested minor are converted to their internal representation. -/
def nativePolicy : MinorRequest (Index D E) := pullbackMinorRequest (indexEquiv D E)
  (matrixMinorRequest D E (manuscriptProxyFuel n))

/-- Causal stream of requests and returned values (or restarts). -/
def nativeHistory (us : List (Index D E)) : List (Index D E × Option ℚ) :=
  let _ := requestWordOrder D E
  serviceEventsFrom (nativePolicy D E) RequestTrace.start us

/-- The chronological response function reads only each input prefix and returns exactly
one response per query. Its correctness clauses use the externally specified minor type. -/
theorem nativeHistory_correct (hn : 1 ≤ n) (hrows : d+e=n) (us : List (Index D E)) :
    let exp := onlineMinorBitPolynomial.eval n
    let history := nativeHistory D E us
    history.map Prod.fst = us ∧ (∀ j, history.take j = nativeHistory D E (us.take j)) ∧
      restartCount history ≤ 15*n^2*((2*n).log2+1) ∧
      (∀ i q, (i,some q) ∈ history → RAM.ratBits q ≤ 3+2*exp) ∧
      (∀ j, extension n exp (logarithm D E) (history.take j)) := by
  let _ := requestWordOrder D E
  let eqv := indexEquiv D E
  let fuel := manuscriptProxyFuel n
  let l := minorProxy D E fuel
  let proxy := fun u : Index D E ↦ l (eqv u)
  let req := nativePolicy D E
  have htest : RestartTest proxy req := (matrixMinorRequest_restartTest D E fuel).pullback eqv
  have hlogs (u : Index D E) : minorTrueLog D E (eqv u) = logarithm D E u := by
    simp [minorTrueLog, minorMagnitude, evaluatePairMinor_eq, eqv, indexEquiv_minor, logarithm]
  obtain ⟨size, extensions⟩ := serviceEvents_pullback_contract eqv n l (minorTrueLog D E)
    (matrixMinorRequest D E fuel) (matrixMinorRequest_restartTest D E fuel)
    (matrixMinorRequest_common D E fuel hn hrows) us
  refine ⟨serviceEventsFrom_indices req _ us, fun j ↦ serviceEventsFrom_take req _ us j, ?_, size, ?_⟩
  · apply serviceEvents_minor_restartCount D E hn hrows proxy _ req htest us
    intro i
    rw [← hlogs i]
    simpa only [paperGrid, paperRadius, threshold, Nat.cast_pow, Nat.cast_ofNat] using
      minorProxy_close D E fuel (eqv i)
  · intro j
    change extension n _ (logarithm D E) ((serviceEventsFrom req RequestTrace.start us).take j)
    rw [← show (fun u ↦ minorTrueLog D E (eqv u)) = logarithm D E from funext hlogs]
    exact extensions j

/-- Independent public form of the functional on-demand guarantee. The same dimension
polynomial bounds all successfully emitted encodings, over every adaptive request prefix. -/
theorem online_response_policy :
    ∃ P : Polynomial ℕ, ∀ (n d e : ℕ), d+e=n →
      ∀ (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ),
      ∃ respond : List (Index D E) → List (Index D E × Option ℚ),
      ∀ us, (respond us).map Prod.fst = us ∧ (∀ j, (respond us).take j = respond (us.take j)) ∧
        restartCount (respond us) ≤ 15*n^2*((2*n).log2+1) ∧
        (∀ i q, (i,some q) ∈ respond us → RAM.ratBits q ≤ 3+2*P.eval n) ∧
        (∀ j, extension n (P.eval n) (logarithm D E) ((respond us).take j)) := by
  refine ⟨onlineMinorBitPolynomial, fun n d e hrows D E ↦ ?_⟩
  cases n with
  | succ n => exact ⟨nativeHistory D E, nativeHistory_correct D E (Nat.succ_pos _) hrows⟩
  | zero =>
    refine ⟨fun us ↦ us.map (fun i ↦ (i, some (0 : ℚ))), fun us ↦ ?_⟩
    refine ⟨by simp [Function.comp_def], fun j ↦ by simp, by simp [restartCount], ?_, ?_⟩
    · intro i q hq
      obtain ⟨u, _, h⟩ := List.mem_map.mp hq
      have hz : (some (0 : ℚ) : Option ℚ) = some q := congrArg Prod.snd h
      have : q = 0 := (Option.some.inj hz).symm
      subst q; change 3 ≤ 3+2*(onlineMinorBitPolynomial.eval 0); omega
    · intro j
      apply zeroHistory_extension
      intro u
      have hu : |(minor D E u.val : ℝ)| = 1 := by exact_mod_cast zeroColumns_unitMinor D E u
      simp [logarithm, hu]

end MinorLog
end OracleSpec
end LinearProgramming
end Optimization
end OAI
