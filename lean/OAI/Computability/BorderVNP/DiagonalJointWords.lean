import OAI.Computability.BorderVNP.DiagonalJointSchedule
import OAI.Computability.BorderVNP.ShortenPublicPaddedWords

/-! # Word capacities on the stretched schedule

All counts of polynomial size in the full batch and length, including the
public tallies and private entry multiplicities, fit the selected word power.
The actual sorter-port estimate bounds that word by the processor length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing PackedHistoryCircuit.Normalized

universe u

/-- A squared logarithmic word transports all fixed polynomials in the
combined input and batch size, with one threshold for every positive batch. -/
theorem eventually_polynomial_words (C d E : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      C*(r*n+1)^d < 2^((logWidth r n)^(E+2)) := by
  filter_upwards [eventually_ge_atTop (2^(C+d+2)),eventually_ge_atTop 1] with n threshold hn
  intro r hr
  let L := logWidth r n
  have logEq : L = Nat.clog 2 (2*n*r) := Shortening.PublicCapacity.public_logWidth n r
  have wide : 2^(C+d+2) ≤ 2*n*r :=
    threshold.trans ((show n ≤ 2*n by omega).trans (Nat.le_mul_of_pos_right _ hr))
  have lower : C+d+2 ≤ L := by
    rw [logEq,← Nat.clog_pow 2 (C+d+2) (by decide)]
    exact Nat.clog_mono_right 2 wide
  have rn : r*n+1 ≤ 2*n*r := by
    rw [Nat.mul_comm r n]
    nlinarith only [Nat.mul_pos hn hr]
  have field : r*n+1 ≤ 2^L := rn.trans (logEq ▸ Nat.le_pow_clog (by decide) _)
  have widen : d*L+2*L ≤ L^2 := by
    have h := Nat.mul_le_mul_right L (show d+2 ≤ L by omega)
    simpa only [Nat.add_mul,pow_two] using h
  have square : C+L*d < L^2 := by rw [Nat.mul_comm L d]; omega
  have width : L^2 ≤ L^(E+2) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    C*(r*n+1)^d ≤ 2^C*(2^L)^d :=
      Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_left field _)
    _ = 2^(C+L*d) := by rw [pow_add,pow_mul]
    _ < 2^(L^(E+2)) := Nat.pow_lt_pow_right (by decide) (square.trans_le width)

variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
variable {S : SiteSchedule e} {a extra : ℕ} {s : EpochScales S a extra} {E d Q A B j : ℕ}

/-- The machine, tally, and private-multiplicity words fit their fields and
the true processor ceiling simultaneously. -/
theorem JointSchedule.eventually_word_capacity (b : JointSchedule.{u} s (E+1) d Q A B j) (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let value := C*(r*n+1)^k
      logWidth r n ≤ b.physical.word n ∧ b.physical.word n ≤ n ∧
        value < 2^b.physical.word n ∧ value < 2^b.physical.tally n ∧
        value < 2^b.physical.multBits n := by
  filter_upwards [eventually_polynomial_words C k E,(b.machine.ports 1).stretched b.rho_omega.le,
    eventually_ge_atTop 1] with n words ports hn
  let r := stretch b.ρ n
  let L := logWidth r n
  have hr := stretch_one b.ρ n
  have hl : 1 ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from Shortening.PublicCapacity.public_logWidth n r]
    exact (show 1 ≤ Nat.clog 2 2 by decide).trans
      (Nat.clog_mono_right _ (by nlinarith only [Nat.mul_le_mul hn hr] : 2 ≤ 2*n*r))
  have cap : L^(E+2) ≤ n := by
    change 1*TeamContraction.Wires.innerWidth r 64 (L^(E+2)) _ (L^(E+2)+1) ≤ n at ports
    unfold TeamContraction.Wires.innerWidth at ports
    omega
  have fit := words r hr
  exact ⟨Nat.le_self_pow (by omega) _,cap,fit,fit,fit⟩

end Diagonal

end BorderVNP
end Computability
end OAI
