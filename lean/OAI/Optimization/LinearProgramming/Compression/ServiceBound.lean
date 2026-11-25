import OAI.Optimization.LinearProgramming.OracleSpec.Companion
import OAI.Optimization.LinearProgramming.Compression.ServiceHistory

/-! Manuscript restart count expressed in the integer units of the sealed service contract. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.OracleSpec

/-- The logarithmic count uses an absolute constant of fifteen in the public integer budget. -/
theorem restart_count_le_contract {n r : ℕ} (hn : 1 ≤ n)
    (hr : (r : ℝ) ≤ (7*(n : ℝ)^2+8)*Real.logb 2 (n+1)) :
    r ≤ 15*n^2*((2*n).log2+1) := by
  have hm : n+1 ≤ 2*n := by omega
  have hp : (n : ℝ)+1 ≤ (2 : ℝ)^((2*n).log2+1) := by
    exact_mod_cast hm.trans (Nat.lt_log2_self.le : 2*n ≤ 2^((2*n).log2+1))
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by positivity : 0 < (n:ℝ)+1) hp
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2), mul_one] at hlog
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpoly : 7*(n : ℝ)^2+8 ≤ 15*(n : ℝ)^2 := by nlinarith [sq_nonneg ((n : ℝ)-1)]
  have hnonneg : 0 ≤ Real.logb 2 ((n : ℝ)+1) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  exact_mod_cast hr.trans (mul_le_mul hpoly hlog hnonneg (by positivity))

/-- Every actual chronological history of the generator policy has the paper's restart count
against the concrete public logarithms. Adaptivity of the request list is unrestricted. -/
theorem serviceEvents_minor_restartCount {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ)
    (E : Matrix (Fin e) (Fin n) ℚ) (hn : 1 ≤ n) (hrows : d+e=n)
    [DecidableEq (MinorLog.Index D E)] (proxy : MinorLog.Index D E → ℝ)
    (herror : ∀ i, |proxy i - MinorLog.logarithm D E i| ≤ 1 / (2:ℝ)^(MinorLog.threshold n+7))
    (request : MinorRequest (MinorLog.Index D E)) (htest : RestartTest proxy request)
    (us : List (MinorLog.Index D E)) :
    MinorLog.restartCount (serviceEventsFrom request RequestTrace.start us) ≤
      15*n^2*((2*n).log2+1) := by
  have he := serviceEvents_restartCount request RequestTrace.start us
  change (RequestTrace.replay request us).restarts = 0 + _ at he
  rw [zero_add] at he
  rw [← he]
  apply restart_count_le_contract hn
  apply RequestTrace.restarts_le proxy request htest
  intro J hJ
  apply dissociated_minor_card_le D E hn hrows (Rat.castHom ℝ)
    (fun i : MinorLog.Index D E ↦ (MinorLog.indexEquiv D E i).val) J proxy _ _ hJ
  · intro i _
    rw [MinorLog.indexEquiv_minor]
    change ((MinorLog.minor D E i.val : ℚ) : ℝ) ≠ 0
    exact_mod_cast i.property
  · intro i _
    change |proxy i - Real.logb 2 (|((pairMinorValue D E (MinorLog.indexEquiv D E i).val : ℚ):ℝ)|)| ≤ _
    rw [MinorLog.indexEquiv_minor]
    exact herror i

end Compression
end LinearProgramming
end Optimization
end OAI
