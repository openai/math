import OAI.Computability.VPVNP.LiveHeaderSchedule
import OAI.Computability.VPVNP.CursorBounds
import OAI.Computability.VPVNP.RAMSiteBounds

/-!
# Choosing the site exponent after the header sizes

Both the read-and-copy clock and the reserved scratch size are polynomial in
quantities fixed before the address exponent is chosen. Thus the prescribed
physical processor array and the word address space suffice simultaneously.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderSchedule

open Filter CursorBounds
open scoped Topology

theorem limit_le_cost (s : Sizes) (base : ℕ) : limit s base ≤ base + costBound s := by
  rw [limit_eq]
  unfold costBound callBound
  omega

theorem field_le_cost (s : Sizes) :
    s.h+2 ≤ costBound s ∧ s.advice ≤ costBound s ∧ (s.h+1)*s.delta ≤ costBound s ∧
      s.e ≤ costBound s ∧ s.config ≤ costBound s := by
  unfold costBound callBound
  omega

private theorem pow_le_processorCount (B n : ℕ) : n^B ≤ processorCount B n := by
  calc
    n^B ≤ (2^(Nat.clog 2 n))^B := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    _ = processorCount B n := by rw [← pow_mul,Nat.mul_comm]; rfl

/-- A single lower bound on B works for all sufficiently large lengths.
Its choice uses only the already selected header sizes. -/
theorem eventually_resources {S : ℕ → Sizes}
    (hh : PolynomiallyBounded fun n => (S n).h) (hd : PolynomiallyBounded fun n => (S n).delta)
    (ha : PolynomiallyBounded fun n => (S n).advice) (he : PolynomiallyBounded fun n => (S n).e)
    (hc : PolynomiallyBounded fun n => (S n).config) :
    ∃ B₀, ∀ B ≥ B₀, ∀ᶠ n : ℕ in atTop,
      costBound (S n) < processorCount B n ∧
      limit (S n) (processorCount B n) < 2 ^ wordBits B n := by
  obtain ⟨A,d,N,hbound⟩ := polynomial_cost hh hd ha he hc
  refine ⟨d+1, fun B hB => ?_⟩
  filter_upwards [eventually_ge_atTop (max N (A+1))] with n hn
  have hN := (le_max_left N (A+1)).trans hn
  have hA := (le_max_right N (A+1)).trans hn
  have hnpos : 0 < n := by omega
  have hcost : costBound (S n) < processorCount B n := by
    calc
      _ ≤ A * n^d := hbound n hN
      _ < n^(d+1) := by rw [pow_succ, Nat.mul_comm A (n^d)]; exact Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pow_pos hnpos)
      _ ≤ n^B := Nat.pow_le_pow_right hnpos hB
      _ ≤ _ := pow_le_processorCount B n
  refine ⟨hcost, ?_⟩
  have hw : addressBits B n + 1 ≤ wordBits B n := by
    unfold wordBits
    generalize addressBits B n = r
    nlinarith [Nat.zero_le (r*r),Nat.zero_le (r*r*r),Nat.zero_le (r*r*r*r)]
  have hdouble : processorCount B n + processorCount B n ≤ 2 ^ wordBits B n := by
    simpa [processorCount,pow_succ,Nat.mul_two] using Nat.pow_le_pow_right (by decide : 0 < 2) hw
  exact (limit_le_cost ..).trans_lt ((Nat.add_lt_add_left hcost _).trans_le hdouble)

end LiveHeaderSchedule

end VPVNP
end Computability
end OAI
