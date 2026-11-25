import OAI.Computability.IntegerMultiplication.Echo.Global

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Echo
open Finset Scale Param IntegerMultiplication.Fourier Cap
noncomputable section
-- denominators envelopes
variable {n:ℕ} (h:Season n)
include h
theorem readLoad :
    Cap.space (criterion n) ≤ 2^P n := by
  change landscape n ≤ _
  rw [h.volume]
  unfold load
  apply Nat.pow_le_pow_right (by decide)
  exact le_trans (split_hi n) (wall_small n)
theorem read_size :
    Cap.space (modulus n) ≤ 2^P n := by
  apply le_trans _ (readLoad h)
  unfold Cap.space
  exact prod_le_prod (s:=univ) (f:=modulus n) (g:=criterion n) fun i _=>pitch h i
theorem read_r :
    ((Cap.space (criterion n)):ℝ)≤ hi n 1 := by simpa [hi] using
    (show ((Cap.space (criterion n)):ℝ) ≤ (2:ℝ)^P n by exact_mod_cast readLoad h)

theorem alias_ (u) (x : Along (criterion n)) {B:ℝ} (v:Bound x B) (q:0≤B):
    Gap (desired h u x) (Exact n u x) (err n*hi n 4*B) := by
  have e:= sensitivity (criterion n)
    (fun i=> ideal (s:=modulus n i) (criterion n i) u)
    (fun i=> port (pitch h i) (D n i) (L n) (J n) (K n) u)
    (invp n).le (err1 n)
    (fun i a b=> consts_n i u a b)
    (fun i a b=> nearly h i u a b)
    v
  rw [wished]
  apply e.mono
  have L : lanes n ≤ P n := Nat.le_self_pow (by decide) _
  have a : (2:ℝ)^lanes n ≤ hi n 1 := by unfold hi; apply pow_le_pow_right₀ (by norm_num); omega
  have b : (lanes n:ℝ)≤ hi n 1 := le_trans
    (by exact_mod_cast (Nat.lt_pow_self (a:=2) (n:=lanes n) (by decide)).le) a
  have E : 0≤err n:=(invp _).le
  calc
    _ ≤ hi n 1*(hi n 1*hi n 1*err n*B) := by
      gcongr
      all_goals first| linarith [hi1 n 1]|exact read_r h
    _ = err n*hi n 3* B := by rw [show hi n 3 = hi n (1+1+1) from rfl,← heightA,← heightA]; ring
    _ ≤ _ := by gcongr; exact hi_mono _ (by decide :3≤4)

-- normalized gain of ideal full source dft
omit h in
theorem strand_sub (K:Square (criterion n)) (x y:Along (criterion n)):
    strand (criterion n) K (x-y)=strand (criterion n) K x - strand (criterion n) K y := by
  classical
  funext i
  simp only [strand,Pi.sub_apply,mul_sub,sum_sub_distrib]
theorem perfection (u) (x:Along (criterion n)) {B:ℝ} (v:Bound x B) (q:0≤B):
    Bound (Exact n u x) (hi n 1*B) := by
  have h₁ := segment (criterion n) (fun i=>ideal (s:=modulus n i) (criterion n i) u)
    v 1 (fun i z b=>consts_n i u z b) zero_le_one q
  apply h₁.mono
  rw [one_pow,one_mul]
  exact mul_le_mul_of_nonneg_right (read_r h) q
theorem perfectionGap (u) (x y:Along (criterion n)) {B:ℝ} (v:Gap x y B) (q:0≤B):
    Gap (Exact n u x) (Exact n u y) (hi n 1*B) := by
  have t:= perfection h u (x-y) v q
  change Bound (Exact _ _ x - Exact _ _ y) _
  unfold Exact at *; rw [← strand_sub]
  exact t
end
end Echo

end IntegerMultiplication
end Computability
end OAI
