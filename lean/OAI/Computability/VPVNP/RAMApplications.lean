import OAI.Computability.VPVNP.CursorBounds
import OAI.Computability.VPVNP.RAMSortAddressBounds
import OAI.Computability.VPVNP.RAMValidatorPaths

/-!
# The live and virtual applications of the RAM transcript lemma

The live processors use a private call clock `n^10000`. The processors
of the virtual RAM use `n^10`. Both inherit the same quartic word width.
The bounds below hold on every local incident vector and branch stream,
including those obtained from a tensor expansion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open Filter Compression CursorBounds RAMLayout

/-- Enough word space for every record and for the physical bit addresses,
together with the numerical bounds used by the local validator clock. -/
structure ProcessorBudget (n d e w : ℕ) : Prop where
  tags : 2 ≤ w
  capFits : 2^d * 2^e < 2^w
  addresses : RAMSort.addressEnvelope (2+e) d w < 2^w
  word_le : w ≤ n
  bucket_le : 2^e ≤ 2*n
  phase_le : 2+e+d+1 ≤ n

private theorem eventually_processorBudget {B : ℕ} (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ d e, d ≤ (B+2)*Nat.clog 2 n → 2^e ≤ 2*n →
      ProcessorBudget n d e (CursorBounds.wordBits B n) := by
  filter_upwards [eventually_ge_atTop (2^(B+6)),
    eventually_word_stage_le B (B+6)] with n hn hw
  intro d e hd hH
  have hnpos : 0 < n := (Nat.two_pow_pos _).trans_le hn
  have hr := log2_le_addressWidth hB n
  have hl := clog_le_log2_succ n
  have hd' := hd.trans (Nat.mul_le_mul_left (B+2) hl)
  have he := (Nat.le_log2 (by omega : 2*n ≠ 0)).mpr hH
  rw [Nat.log2_two_mul hnpos.ne'] at he
  have hsum : 2+e+d+1 ≤ (B+6)*(n.log2+1) := by rw [Nat.add_mul] at hd' ⊢; omega
  obtain ⟨hword, hstage⟩ := hw (addressWidth B n) _ (Nat.mul_le_mul_left _ hl) hsum
  have hk := ((Nat.le_log2 hnpos.ne').mpr hn).trans hr
  have hscale := hsum.trans (Nat.mul_le_mul_left (B+6) (Nat.succ_le_succ hr))
  change 2+e+d+1 ≤ (B+6)*(addressWidth B n + 1) at hscale
  have hde : d+e ≤ (B+6)*(addressWidth B n + 1) := by omega
  obtain ⟨htags, hcap⟩ := RAMSerialization.word_capacity _ _ _ _ hde (by omega)
  have hsq : 2+e+d ≤ (addressWidth B n+10)^2 := by
    rw [pow_two]
    exact (by omega : 2+e+d ≤ (B+6)*(addressWidth B n + 1)).trans
      (Nat.mul_le_mul (by omega) (by omega))
  exact ⟨htags, hcap, RAMSort.addressEnvelope_lt_paperWord hsq, hword, hH, hstage⟩

private theorem bucket_le_twice {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    2^bucketExponent x n ≤ 2*n := by
  have hh := (bucketExponent_bounds hx hn).2
  have hpow : (n:ℝ)^x ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx'
  exact_mod_cast hh.trans (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 2))

/-- One eventual threshold works for both processors' message formats and
their cutoffs in §§10–12. -/
theorem eventually_bothProcessorBudgets {B : ℕ} (hB : 1 ≤ B) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      ProcessorBudget n (addressWidth B n) (bucketExponent (1-δ) n) (CursorBounds.wordBits B n) ∧
      ProcessorBudget n (virtualBits B n) (roundedUp 1 4 n) (CursorBounds.wordBits B n) := by
  filter_upwards [eventually_processorBudget hB, eventually_ge_atTop 1] with n h hn
  refine ⟨h _ _ (Nat.mul_le_mul_right _ (by omega)) (bucket_le_twice (by linarith) (by linarith) hn),
    h _ _ (virtualBits_le ..) ?_⟩
  rw [roundedUp_eq]
  exact bucket_le_twice (by norm_num) (by norm_num) hn

/-- Section 10's live `n^100030` bound and Section 12's virtual `n^130`
bound apply uniformly to the concrete instruction table and all local input
values at the respective lengths. -/
theorem ProcessorBudget.validate_clock {n d e w p r k u : ℕ} (b : ProcessorBudget n d e w)
    (M : PrivateRAM.Machine w p r k) (hn : 2048 ≤ n) (hk : k+2 ≤ n) (hu : 1 ≤ u)
    (initial header : Word w) (v : Fin (2^d)) (inc : Fin (width d (2^e) w) → Bool)
    (bits : List Bool) :
    (M.validateIncident (n^u) initial header b.tags b.capFits v inc bits).2 ≤ n^(10*u+30) :=
  M.validateIncident_clock n u _ _ _ _ _ _ _ hn hu hk b.word_le b.bucket_le b.phase_le

end BurstRAM

end VPVNP
end Computability
end OAI
