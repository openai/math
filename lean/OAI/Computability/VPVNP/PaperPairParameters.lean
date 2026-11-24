import OAI.Computability.VPVNP.CursorBranchBudget
import OAI.Computability.VPVNP.CompressorRecordsCursorCoordinates
import OAI.Computability.VPVNP.RAMApplications
import OAI.Computability.VPVNP.PolynomialBounds

/-!
# Integer parameters of the fixed live and virtual machines

The rational exponents chosen by the compressor have fixed positive
numerators and denominators. Using them in the integer floor and ceiling
algorithms gives exactly the analytic block and bucket counts of §9.1 at
every length. After choosing the address exponent, one threshold supplies
the live and virtual word capacities, the exponent no-overflow margin,
and enough fresh lane coordinates.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram
universe v

open Compression CursorBounds CursorNetwork BurstRAM Filter

/-- A positive rational strictly below one in the fixed program's operand format. -/
structure Ratio (x : ℝ) where
  /-- Positive integer numerator in the program's representation of a ratio between zero and
  one. -/
  num : ℕ
  /-- Positive integer denominator, strictly larger than the numerator, used by the program's
  rounded integer arithmetic. -/
  den : ℕ
  num_pos : 0 < num
  den_pos : 0 < den
  less : num < den
  value : (num : ℝ) / den = x

/-- Encodes a positive rational below one by its natural numerator and denominator, preserving
its value as a real number. -/
def Ratio.ofRat (x : ℚ) (hp : 0 < x) (hl : x < 1) : Ratio (x : ℝ) := by
  have hnum := Rat.num_pos.mpr hp
  have hcast : (x.num.toNat : ℝ) = (x.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnum.le
  have hden : 0 < (x.den : ℝ) := by exact_mod_cast x.den_pos
  have hv : (x.num.toNat : ℝ) / x.den = (x : ℝ) := by rw [hcast, Rat.cast_def]
  have hlt : (x.num.toNat : ℝ) / x.den < 1 := by rw [hv]; exact_mod_cast hl
  have hlt' := (div_lt_iff₀ hden).mp hlt
  rw [one_mul] at hlt'
  exact ⟨x.num.toNat,x.den,by omega,x.den_pos,by exact_mod_cast hlt',hv⟩

variable {C₂ : ℕ}

/-- Operand pair representing the block exponent θ in the fixed program. -/
def blockRatio (u : PairExponents C₂) : Ratio (u.θ : ℝ) :=
  Ratio.ofRat u.θ u.theta_pos (lt_trans u.theta_lt (by norm_num))

/-- Operand pair representing the live-bucket exponent 1 − δ in the fixed program. -/
def liveRatio (u : PairExponents C₂) : Ratio (1-(u.δ : ℝ)) := by
  have h : (1-(u.δ : ℝ)) = ((1-u.δ : ℚ) : ℝ) := by norm_num
  rw [h]
  exact Ratio.ofRat (1-u.δ) (by linarith [u.delta_lt,u.theta_lt]) (by linarith [u.delta_pos])

theorem blockRatio_floor (u : PairExponents C₂) (n : ℕ) :
    roundedDown (blockRatio u).num (blockRatio u).den n = blockCount (u.θ : ℝ) n := by
  rw [roundedDown_eq, (blockRatio u).value]

theorem liveRatio_ceil (u : PairExponents C₂) (n : ℕ) :
    roundedUp (liveRatio u).num (liveRatio u).den n = bucketExponent (1-(u.δ : ℝ)) n := by
  rw [roundedUp_eq, (liveRatio u).value]

/-- The power of two obtained by rounding (1 − δ) log₂ n upward to an integer using the
live-ratio operands. -/
def liveCapacity (u : PairExponents C₂) (n : ℕ) :=
  2^(roundedUp (liveRatio u).num (liveRatio u).den n)

theorem liveCapacity_eq (u : PairExponents C₂) (n : ℕ) : liveCapacity u n = liveBucket (u.δ : ℝ) n := by
  rw [liveCapacity, liveRatio_ceil]
  rfl

theorem liveCapacity_polynomial (u : PairExponents C₂) : PolynomiallyBounded (liveCapacity u) := by
  have hd : 0 ≤ (u.δ : ℝ) := by exact_mod_cast u.delta_pos.le
  have hd' : (u.δ : ℝ) ≤ 1 := by exact_mod_cast (show u.δ ≤ 1 by linarith [u.theta_lt,u.delta_lt])
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_bothProcessorBudgets (B := 1) (by decide) hd hd')
  exact ((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).of_eventually_le N
    (fun n hn => by rw [liveCapacity, liveRatio_ceil]; exact (hN n hn).1.bucket_le)

/-- Any fixed number of probes fits the live bucket at sufficiently large lengths. -/
theorem eventually_liveCapacity_ge (u : PairExponents C₂) (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, M ≤ liveCapacity u n := by
  let x := liveRatio u
  filter_upwards [eventually_ge_atTop ((2^x.den)^M+1)] with n hn
  have hn0 : 0 < n := by omega
  have hbase : 1 < 2^x.den := Nat.one_lt_two_pow x.den_pos.ne'
  have hpow : n ≤ n^x.num := by simpa using Nat.pow_le_pow_right hn0 x.num_pos
  have hcl : M < Nat.clog (2^x.den) (n^x.num) := (Nat.lt_clog_iff_pow_lt hbase).mpr (hn.trans hpow)
  exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) hcl.le)

private theorem n_pow_le_sites (B n : ℕ) : n^B ≤ processorCount B n := by
  calc
    _ ≤ (2^(Nat.clog 2 n))^B := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) n) B
    _ = _ := by rw [← pow_mul, Nat.mul_comm]; rfl

/-- Address/counter and geometry premises in the physical local certificate,
before any particular algebra, path or prime is chosen. -/
theorem eventually_numeric {k : Type v} [Field k] {S : BlockSchedule k} (T : S.Templates)
    (u : PairExponents T.growthConstant) (B a : ℕ) (hB : max S.laneBits 5 ≤ B) (ha : 1 ≤ a) :
    ∀ᶠ n : ℕ in atTop,
      4 ≤ wordBits B n ∧ processorCount B n * liveCapacity u n < 2^wordBits B n ∧
      4*n ≤ processorCount B n ∧ n^a-1+2*addressBits B n ≤ 2*n^a ∧
      1 < virtualBits B n ∧ blockCount (u.θ : ℝ) n * S.laneBits ≤ virtualBits B n := by
  have hd : 0 ≤ (u.δ : ℝ) := by exact_mod_cast u.delta_pos.le
  have hd' : (u.δ : ℝ) ≤ 1 := by exact_mod_cast (show u.δ ≤ 1 by linarith [u.theta_lt,u.delta_lt])
  have h5 : 5 ≤ B := (le_max_right ..).trans hB
  filter_upwards [eventually_bothProcessorBudgets (B := B) (by omega) hd hd',
    eventually_pairBranchBounds.{v,0} T u B hB, eventually_polylog_le (2*B) 1,
    eventually_ge_atTop 4] with n budgets branch hsmall hn
  have hn0 : 0 < n := by omega
  have hrs : 2*addressBits B n ≤ n := calc
    _ = (2*B)*Nat.clog 2 n := by rw [addressBits, addressWidth, Nat.mul_assoc]
    _ ≤ (2*B)*(n.log2+1) := Nat.mul_le_mul_left _ (clog_le_log2_succ n)
    _ ≤ n := by simpa only [pow_one] using hsmall
  have height : n ≤ n^a := by simpa using Nat.pow_le_pow_right hn0 ha
  have hR : 4*n ≤ processorCount B n := calc
    _ ≤ n*n := Nat.mul_le_mul_right n hn
    _ = n^2 := (sq n).symm
    _ ≤ n^B := Nat.pow_le_pow_right hn0 (by omega)
    _ ≤ processorCount B n := n_pow_le_sites B n
  have hw : 4 ≤ wordBits B n := by
    change 4 ≤ (addressBits B n+10)^4
    nlinarith [Nat.pow_le_pow_left (by omega : 1 ≤ addressBits B n + 10) 4,
      Nat.pow_le_pow_right (by omega : 0 < addressBits B n+10) (by decide : 1 ≤ 4)]
  have hc := budgets.1.capFits
  rw [liveCapacity, liveRatio_ceil]
  exact ⟨hw,hc,hR,by omega,branch.1,branch.2.1⟩

/-- Number the reserved lane coordinates after the base coordinates, using
exactly the number consumed by the selected blocks. -/
def laneLabels (D lanes : ℕ) (h : lanes ≤ D) : Fin D ≃ Fin (D-lanes) ⊕ Fin lanes :=
  (finCongr (Nat.sub_add_cancel h).symm).trans (CursorNetwork.cursorCoordinateLabels (D-lanes) lanes)

end LiveProgram

end VPVNP
end Computability
end OAI
