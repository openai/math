import OAI.Optimization.LinearProgramming.PriceGame.LearningPool
import OAI.Optimization.LinearProgramming.PriceGame.LearningBits

/-! A common rational grid for every expert fed to every adaptive trial. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Pool

theorem entry_common_grid {N R : ℕ} {ps : List (Probe N)} {e : Expert N}
    (he : e ∈ batch N R ps) (i : Fin N) : (e.raw i).den ∣ Bits.commonDenominator := by
  obtain ⟨s, _, h⟩ := List.mem_flatMap.mp he
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
  change (Compact.unpack s v i).den ∣ _
  by_cases hs : i ∈ s.sources
  · simpa only [Compact.unpack, ite_eq_left hs] using
      Bits.generated_common_denominator hv (Skeleton.card_sources_le s) (Compact.index s i)
  · simp [Compact.unpack, hs]

theorem catalogue_entry_grid {N R : ℕ} (hist : ℕ → List (Probe N)) (T : ℕ) (e : Expert N)
    (he : e ∈ Catalog.entries (fun t => batch N R (hist t)) T) (i : Fin N) :
    (e.raw i).den ∣ Bits.commonDenominator ∧ |e.raw i| ≤ (R+1 : ℕ) := by
  induction T with
  | zero => simp [Catalog.entries] at he
  | succ t ih =>
    rcases List.mem_append.mp he with hold | hnew
    · exact ih hold
    · obtain ⟨hl, hu⟩ := entry_box hnew i
      exact ⟨entry_common_grid hnew i, by rw [abs_of_nonneg (zero_le_one.trans hl)]; simpa using hu⟩

end Pool
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
