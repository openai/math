import OAI.Computability.NearSquareRoot.PhysicalWalshPaddingHeader
import OAI.Computability.NearSquareRoot.KernelComputableAddress
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Explicit cutoff for sparse spectator padding

A lower bound on the logarithm makes the total selected width small enough
to reserve one spectator bit for every fanout bit at every recursion level.
The bound works for every template radix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.SparseCutoff

/-- A dyadic cutoff uniform for all sparsity coefficients at most `G+1`. -/
def threshold (G W : ℕ) := 2^(2*((W+1)*(G+1)))

theorem primrec_threshold : Primrec₂ threshold :=
  (KernelComputableAddress.primrec_pow (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.snd) (Primrec.succ.comp Primrec.fst)))).to₂

theorem log_bound {G W k : ℕ} (hk : threshold G W ≤ k) :
    (W+1:ℝ)*(G+1) ≤ Real.log (2+k) := by
  let n := (W+1)*(G+1)
  have hnum : (2:ℝ)^(2*n) ≤ (k:ℝ) := by exact_mod_cast hk
  have logle := Real.log_le_log (by positivity : 0 < (2:ℝ)^(2*n))
    (hnum.trans (by linarith : (k:ℝ) ≤ 2+k))
  rw [Real.log_pow] at logle
  have log2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have factor := mul_le_mul_of_nonneg_left log2 (by positivity : 0 ≤ (2:ℝ)*(n:ℝ))
  have H : (n:ℝ) ≤ Real.log (2+k) := by push_cast at logle; linarith
  exact_mod_cast H

theorem selected_bound {G W k s : ℕ} (hk : threshold G W ≤ k)
    {g : ℝ} (hg : 0 < g) (cap : g ≤ G+1)
    (hs : (s:ℝ) ≤ g*k/Real.log (2+k)) : (W+1)*s ≤ k := by
  have lower : (W+1:ℝ)*g ≤ Real.log (2+k) :=
    (mul_le_mul_of_nonneg_left cap (by positivity)).trans (log_bound hk)
  have hlog : 0 < Real.log (2+(k:ℝ)) := (mul_pos (by positivity) hg).trans_le lower
  have e := (mul_le_mul_of_nonneg_left lower (Nat.cast_nonneg s)).trans ((le_div_iff₀ hlog).mp hs)
  have H : ((W+1:ℝ)*s)*g ≤ (k:ℝ)*g := by linarith only [e]
  exact_mod_cast (le_of_mul_le_mul_right H hg)

theorem fanout {G W k s : ℕ} (A : ℕ) (hk : threshold G W ≤ k) {g : ℝ} (hg : 0 < g)
    (cap : g ≤ G+1) (hs : (s:ℝ) ≤ g*k/Real.log (2+k)) :
    W^WalshPadding.depth A s ≤ 2^(k-s) := by
  have bound := selected_bound hk hg cap hs
  rw [Nat.succ_mul] at bound
  have hd : WalshPadding.depth A s ≤ s := (Nat.log_le_self _ _).trans (Nat.div_le_self ..)
  calc
    W^WalshPadding.depth A s ≤ (2^W)^WalshPadding.depth A s :=
      Nat.pow_le_pow_left W.lt_two_pow_self.le _
    _ = 2^(W*WalshPadding.depth A s) := (pow_mul ..).symm
    _ ≤ 2^(k-s) := Nat.pow_le_pow_right (by decide) (by have h := Nat.mul_le_mul_left W hd; omega)

theorem geometry {G W k s : ℕ} (A : ℕ) (hW : 0 < W) (hk : threshold G W ≤ k)
    {g : ℝ} (hg : 0 < g) (cap : g ≤ G+1) (hs : (s:ℝ) ≤ g*k/Real.log (2+k)) :
    s ≤ k ∧ PaddingHeader.extra A W k s ≤ 2^k := by
  have width := selected_bound hk hg cap hs
  rw [Nat.succ_mul] at width
  have small : s ≤ k := by omega
  have doubled := WalshPadding.paddedRows_le_double hW (fanout A hk hg cap hs)
  refine ⟨small,?_⟩
  calc
    PaddingHeader.extra A W k s ≤ 2^(k-s)*2^s := Nat.mul_le_mul_right _ (by
      omega)
    _ = 2^k := by rw [← pow_add, Nat.sub_add_cancel small]

theorem geometry_one {W k s : ℕ} (A : ℕ) (hW : 0 < W) (hk : threshold 0 W ≤ k)
    (hs : (s:ℝ) ≤ k/Real.log (2+k)) : s ≤ k ∧ PaddingHeader.extra A W k s ≤ 2^k :=
  geometry A hW hk (g := 1) zero_lt_one (by norm_num) (by simpa using hs)

end PhysicalWalsh.SparseCutoff

end NearSquareRoot
end Computability
end OAI
