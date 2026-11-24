import OAI.Computability.VPVNP.LiveVirtualPairStartupBudget
import OAI.Computability.VPVNP.PairLinkSlack

/-!
# Online report budgets from chronological work bounds

A single length threshold covers every report sequence whose total probes are
linear in the input positions times a fixed power of the binary logarithm,
and whose individual bursts have polylogarithmic length. The estimates apply
directly to the concatenated chronological runs, including repeated visits
to the same abstract level.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM Compression CursorNetwork CursorBounds Filter
open private probes_le_length from OAI.Computability.VPVNP.LiveCompressedPairCursorStartup

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

/-- Total probes take at most one sixty-fourth of the live group, and each
report fits both the burst and private clock with the enclosing link costs. -/
theorem eventually_online_of_local_rates (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (_hb : max S.laneBits 5 ≤ b) (rate q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (rs : List (Report (wordBits b n))),
      RAMBuckets.cost Report.probes rs ≤ rate * (pairInput S labels hD).positions * (n.log2+1)^q →
      (∀ r ∈ rs, r.events.length ≤ rate * (n.log2+1)^q) →
      64 * RAMBuckets.cost Report.probes rs ≤ processorCount b n * liveCapacity u n ∧
        ∀ r ∈ rs, r.probes+11 ≤ liveCapacity u n ∧ r.events.length+101 ≤ n := by
  have gap : (3/4 : ℝ) < 1 - (u.δ : ℝ) := by
    have ht := (Rat.cast_lt (K := ℝ)).mpr u.theta_lt
    have hd := (Rat.cast_lt (K := ℝ)).mpr u.delta_lt
    push_cast at ht hd
    linarith
  have global := eventually_absorb_polylog (64 * (rate : ℝ) * (2 * ((b : ℝ)+2))) (2+q)
    gap (by norm_num : (0 : ℝ) < 1)
  have localBound := eventually_absorb_polylog (rate : ℝ) q (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [global,localBound,eventually_pairBurstSlack u 11,
    eventually_polylog_le (rate+101) q,eventually_ge_atTop 2] with n hglobal hlocal hburst hticks hn
  intro base lanes labels hD rs hcost hreport
  rw [pairInput_positions] at hcost
  rw [liveCapacity_eq]
  let R := (processorCount b n : ℝ)
  let log := (n.log2 : ℝ) + 1
  have pos := initialPositions_bound b n hn
  have total : (64 : ℝ) * (RAMBuckets.cost Report.probes rs : ℝ) ≤
      R * (liveBucket u.δ n : ℝ) := calc
    _ ≤ 64 * ((rate : ℝ) * (initialPositions b n : ℝ) * log^q) := by
      dsimp only [log]
      exact_mod_cast Nat.mul_le_mul_left 64 hcost
    _ ≤ 64 * ((rate : ℝ) * ((2*((b : ℝ)+2))*R*(n : ℝ)^(3/4 : ℝ)*log^2) * log^q) := by
      gcongr
    _ = R * ((64*(rate : ℝ)*(2*((b : ℝ)+2)))*(n : ℝ)^(3/4 : ℝ)*log^(2+q)) := by
      rw [pow_add]; ring
    _ ≤ R * (n : ℝ)^(1-(u.δ : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa only [one_mul] using hglobal
    _ ≤ _ := mul_le_mul_of_nonneg_left (liveBucket_bounds (by linarith) (by omega)).1 (Nat.cast_nonneg _)
  dsimp only [R] at total
  refine ⟨by exact_mod_cast total,?_⟩
  intro r hr
  have lengthBound := hreport r hr
  have probes : r.probes ≤ rate * (n.log2+1)^q := (probes_le_length r.events).trans lengthBound
  have hsmall : ((rate * (n.log2+1)^q : ℕ) : ℝ) ≤ (n : ℝ)^(1/2 : ℝ) := by
    push_cast
    simpa only [Real.rpow_zero,mul_one,one_mul] using hlocal
  have live : (rate * (n.log2+1)^q : ℕ) + 11 ≤ liveBucket u.δ n := by
    exact_mod_cast (add_le_add_left hsmall (11 : ℝ)).trans hburst
  have padded : 101 ≤ 101 * (n.log2+1)^q :=
    Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _))
  rw [Nat.add_mul] at hticks
  exact ⟨by omega,by omega⟩

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
