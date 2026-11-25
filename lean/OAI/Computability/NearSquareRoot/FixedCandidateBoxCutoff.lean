import OAI.Computability.NearSquareRoot.FixedCandidateThreshold
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetBox

/-! # Effective space for every pair of Fourier permutation reserve degrees -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open DigitPacking Controlled SynchronizedPermutationBudget

/-- Once the binary logarithm exceeds five, the exponential covers this
quadratic, hence every fixed multiple of the logarithm below that logarithm. -/
private theorem quadratic_dyadic {b : ℕ} (hb : 5 ≤ b) : b*(b+1) ≤ 2^b := by
  induction b, hb using Nat.le_induction with
  | base => decide
  | succ b hb ih =>
    rw [pow_succ]
    have step : (b+1)*(b+1+1) ≤ 2*(b*(b+1)) := by nlinarith
    exact step.trans (by simpa only [Nat.mul_comm 2] using Nat.mul_le_mul_left 2 ih)

def boxCutoff (lo hi : ℕ) := 2^(2246+4*(lo+hi))

theorem boxCutoff_primrec : Primrec₂ boxCutoff :=
  (KernelComputableAddress.primrec_pow (.const 2) (Primrec.nat_add.comp (.const 2246)
    (Primrec.nat_mul.comp (.const 4) (Primrec.nat_add.comp .fst .snd)))).to₂

/-- Both numerical capacity conditions hold at every later width, for any
literal reserves chosen in the enumerated tuple. -/
theorem boxRoom_of_cutoff {k lo hi : ℕ} (h : boxCutoff lo hi ≤ k) :
    8*SynchronizedPermutationBudget.width k ≤ k ∧ payloadBits lo k + payloadBits hi k ≤ k/4 := by
  let b := Nat.log 2 k
  change 2^(2246+4*(lo+hi)) ≤ k at h
  have hpos : 0 < k := (Nat.two_pow_pos _).trans_le h
  have hb : 2246+4*(lo+hi) ≤ b := Nat.le_log_of_pow_le (by decide) h
  have hc : Nat.clog 2 (k+1) ≤ b+1 := Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide) k)
  have q := quadratic_dyadic (b := b) (by omega)
  have e : 2^b ≤ k := Nat.pow_log_le_self 2 hpos.ne'
  have fit (D : ℕ) (hd : D ≤ b) : D*Nat.clog 2 (k+1) ≤ k := (Nat.mul_le_mul hd hc).trans (q.trans e)
  have one : 1 ≤ Nat.clog 2 (k+1) := Nat.clog_pos (by decide) (by omega)
  constructor
  · have := fit 2240 (by omega)
    unfold SynchronizedPermutationBudget.width
    omega
  · apply (Nat.le_div_iff_mul_le (by decide)).mpr
    unfold payloadBits
    calc
      _ = (4*(lo+hi))*Nat.clog 2 (k+1) := by ring
      _ ≤ k := fit _ (by omega)

/-- The small-position branch is used below this literal cutoff. At every larger
width each of the four position factors has the necessary reserve. -/
theorem position_reserves_of_cutoff {k lo hi : ℕ} (h : boxCutoff lo hi ≤ k) :
    payloadBits lo k + payloadBits hi k ≤ k/2-2 := by
  obtain ⟨room,reserves⟩ := boxRoom_of_cutoff h
  unfold SynchronizedPermutationBudget.width at room
  omega

theorem boxPasses_of_cutoff {k lo hi : ℕ} (h : boxCutoff lo hi ≤ k)
    (valid : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k)) : BoxPasses k lo hi :=
  ⟨valid,(boxRoom_of_cutoff h).1,(boxRoom_of_cutoff h).2⟩

/-- The single emitted width test covers the numerical precision and the whole
Fourier batch layout. Every tuple has this guarantee, including guesses whose
transport costs later exceed the useful time or space exponent. -/
theorem guarded_boxPasses (cut lo hi : ℕ → ℕ) (hc : Computable cut) (hl : Computable lo) (hh : Computable hi) :
    ∃ K : ℕ → ℕ, Computable K ∧ (∀ j, 2 ≤ K j) ∧ ∀ j n, K j ≤ n →
      Directory n ∧ 1024+cut j ≤ addressBits n ∧ BoxPasses (addressBits n) (lo j) (hi j) := by
  let budget j := cut j + boxCutoff (lo j) (hi j)
  have computable_budget : Computable budget := Primrec.nat_add.to_comp.comp hc (boxCutoff_primrec.to_comp.comp hl hh)
  obtain ⟨K,hK,hn,ok⟩ := guarded_directory budget computable_budget
  refine ⟨K,hK,hn,fun j n h => ?_⟩
  obtain ⟨directory,large⟩ := ok j n h
  dsimp [budget] at large
  exact ⟨directory,by omega,boxPasses_of_cutoff (by omega) directory⟩

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
