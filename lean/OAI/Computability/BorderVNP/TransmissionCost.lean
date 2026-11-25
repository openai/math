import OAI.Computability.BorderVNP.TransmissionStraight
import Mathlib.Algebra.BigOperators.Intervals

/-! # Sparse iteration cost for the physical interval directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

/-- Charge each successful iteration separately. In the public directory an unrelated
range has constant cost, even if its width is large. -/
theorem loop_runs {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    (cursor bound : Reg) (body : Code) (hi : ℕ) (cost : ℕ → ℕ) (Inv : ℕ → Bank w → Memory w → Prop)
    (fields : ∀ i s m, Inv i s m → (s cursor).val = i ∧ (s bound).val = hi)
    (step : ∀ i < hi, ∀ s m, Inv i s m → ∃ es t mt, Runs pub macros body s m es t mt ∧
      Inv (i+1) t mt ∧ traceCost es ≤ cost i)
    (i : ℕ) (start : i ≤ hi) (s : Bank w) (m : Memory w) (init : Inv i s m) :
    ∃ es t mt, Runs pub macros (.whileLt cursor bound body) s m es t mt ∧
      Inv hi t mt ∧ traceCost es ≤ (∑ j ∈ Finset.Ico i hi, (cost j+1)) + 1 := by
  obtain ⟨hx,hy⟩ := fields i s m init
  by_cases he : i = hi
  · rw [he] at init ⊢
    exact ⟨_,s,m,.whileDone (show ¬ (s cursor).val < (s bound).val by omega),init,by simp [traceCost,tick,
      VPVNP.RAMBuckets.cost,TeamTranscript.Action.extra]⟩
  · have hlt : i < hi := by omega
    obtain ⟨es,t,mt,r,inv,hc⟩ := step i hlt s m init
    obtain ⟨fs,z,mz,rest,last,hc'⟩ := loop_runs cursor bound body hi cost Inv fields step (i+1) hlt t mt inv
    refine ⟨_,z,mz,.whileStep (show (s cursor).val < (s bound).val by omega) r rest,last,?_⟩
    change 1 + traceCost (es ++ fs) ≤ _
    rw [cost_append, Finset.sum_eq_sum_Ico_succ_bot hlt]
    omega
termination_by hi-i

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
