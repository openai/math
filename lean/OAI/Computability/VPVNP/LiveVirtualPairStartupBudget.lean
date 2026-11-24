import OAI.Computability.VPVNP.LiveCompressedPairCursorStartup
import OAI.Computability.VPVNP.LiveVirtualCompressedBudget
import OAI.Computability.VPVNP.PaperPairParameters

/-! # The eight native startup rows fit the compressed pair's burst budget -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM Compression CursorNetwork Filter

theorem eventually_startup_burst {c : ℕ} (u : PairExponents c) (b : Bootstrap)
    (initial phases margin : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin 8, sourceFuel b initial phases n i + margin ≤ liveCapacity u n := by
  obtain ⟨A,hA⟩ := sourceFuel_log b initial phases margin
  have hδ : (u.δ : ℝ) < 1 := by
    exact_mod_cast (show u.δ < 1 by linarith [u.theta_lt,u.delta_lt])
  filter_upwards [eventually_absorb_polylog (A : ℝ) 1 (show (0 : ℝ) < 1-(u.δ : ℝ) by linarith)
      (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop 1] with n small hn i
  simp only [Real.rpow_zero, mul_one, pow_one, one_mul] at small
  have live := (liveBucket_bounds hδ.le hn).1
  rw [liveCapacity_eq]
  apply (hA n i).trans
  exact_mod_cast small.trans live

/-- The verified runs of the eight fixed bootstrap routines supply their own
communication and private instruction bounds. -/
theorem startup_rows_le {w : ℕ} (b : Bootstrap) (initial phases n H cap : ℕ)
    (src : List (Stage × Report w))
    (source : ∀ p ∈ src, ∃ i : Fin 8,
      p.2.probes < sourceFuel b initial phases n i ∧ p.2.events.length < sourceFuel b initial phases n i)
    (burst : ∀ i, sourceFuel b initial phases n i+5 ≤ H)
    (fuel : ∀ i, sourceFuel b initial phases n i+77 ≤ cap) :
    ∀ p ∈ src, p.2.probes+5 ≤ H ∧ p.2.events.length+77 ≤ cap := by
  intro p hp
  obtain ⟨i, probes, events⟩ := source p hp
  exact ⟨(Nat.add_le_add_right probes.le 5).trans (burst i),
    (Nat.add_le_add_right events.le 77).trans (fuel i)⟩

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
