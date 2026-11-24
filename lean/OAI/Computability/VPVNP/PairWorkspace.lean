import OAI.Computability.VPVNP.CursorBranchBudget
import OAI.Computability.VPVNP.CompressorRecordsCursorCoordinates

/-!
# Lane choice and physical addresses of the compressed pair

Use the first virtual address bits for the base, and precisely the last
block coordinates for compression. A fixed polynomial amount of scratch
space per live processor fits in the quartic live word length. The
threshold is chosen before any descriptor or final path is selected.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorBounds Compression Filter

/-- The executable cursor's bit reversal inside each of the two coordinate
blocks is included in the choice of labels. -/
def scheduledLabels (D lanes : ℕ) (h : lanes ≤ D) : Fin D ≃ Fin (D-lanes) ⊕ Fin lanes :=
  (finCongr (Nat.sub_add_cancel h).symm).trans (cursorCoordinateLabels (D-lanes) lanes)

/-- Polynomially many scratch cells per live site, with fixed logarithmic
overhead, can all be represented by distinct live word addresses. -/
theorem eventually_pairWorkspaceFits (b : ℕ) (hb : 1 ≤ b) (C degree logPower : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      C * processorCount b n * n^degree * (n.log2+1)^logPower + 1 < 2 ^ wordBits b n := by
  let K := C.size + degree + logPower + 2
  filter_upwards [eventually_ge_atTop (2^K)] with n hn
  let c := Nat.clog 2 n
  let r := addressBits b n
  have hc : K ≤ c := by
    simpa [c, Nat.clog_pow _ _ (by decide : 1 < 2)] using Nat.clog_mono_right 2 hn
  have hcr : c ≤ r := Nat.le_mul_of_pos_left _ hb
  have hr : K ≤ r := hc.trans hcr
  have hn' : 0 < n := (Nat.two_pow_pos _).trans_le hn
  have hs : n.log2+1 ≤ n := (Nat.log2_lt hn'.ne').mpr Nat.lt_two_pow_self
  have hn2 : n ≤ 2^c := Nat.le_pow_clog (by decide) _
  have hsize : C ≤ 2^C.size := (Nat.lt_size_self C).le
  have hdegree : degree + logPower ≤ r := by dsimp [K] at hr; omega
  have hword : C.size + r + c*(degree+logPower) + 1 < (r+10)^4 := by
    have ht := Nat.mul_le_mul hcr hdegree
    have hs' : C.size ≤ r := by dsimp [K] at hr; omega
    nlinarith only [ht, hs', Nat.zero_le r, Nat.zero_le (r^3), Nat.zero_le (r^4)]
  have hwork : C * processorCount b n * n^degree * (n.log2+1)^logPower ≤
      2^(C.size+r+c*(degree+logPower)) := by
    calc _ ≤ 2^C.size * 2^r * (2^c)^degree * (2^c)^logPower :=
           Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right _ hsize)
             (Nat.pow_le_pow_left hn2 _)) (Nat.pow_le_pow_left (hs.trans hn2) _)
         _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]; ring_nf
  have htwo := Nat.pow_lt_pow_right (by decide : 1 < 2) hword
  apply lt_of_le_of_lt _ htwo
  rw [pow_succ]
  have := Nat.two_pow_pos (C.size + r + c * (degree+logPower))
  omega

/-- A fixed coefficient and the two logarithmic factors in the cursor
directory are eventually absorbed by the live site's quadratic arena. -/
theorem eventually_pairWorkspace_lt_square (b : ℕ) (hb : 5 ≤ b) (C : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      C * processorCount b n * n^2 * (n.log2+1)^2 + 1 < (processorCount b n)^2 := by
  filter_upwards [BurstRAM.eventually_polylog_le (C+1) 2, eventually_ge_atTop 2] with n hc hn
  let R := processorCount b n
  let L := (n.log2+1)^2
  have hR : 0 < R := Nat.two_pow_pos _
  have hL : 0 < L := pow_pos (Nat.succ_pos _) _
  have h5 : n^5 ≤ R := pow_five_le_processorCount n hb
  change (C+1)*L ≤ n at hc
  change C*R*n^2*L+1 < R^2
  calc _ ≤ (C+1)*L*(R*n^2) := by
         nlinarith only [Nat.mul_pos (Nat.mul_pos hR (pow_pos (by omega : 0 < n) 2)) hL]
       _ ≤ n*(R*n^2) := Nat.mul_le_mul_right _ hc
       _ = R*n^3 := by ring
       _ < R*n^5 := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by omega) (by decide)) hR
       _ ≤ R^2 := by rw [pow_two]; exact Nat.mul_le_mul_left _ h5

set_option maxHeartbeats 1200000 in
-- The branch carries the dependent cursor state through the real-to-integer size comparisons.
/-- The initial cursor directory, live header block, expanded placement rows
and final bit array fit simultaneously. The fixed multiplier can cover the
constant record strides and the fixed number of arrays. -/
theorem eventually_pairArenaFitBoth {k : Type*} [Field k] {S : BlockSchedule k}
    (B : S.Templates) (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    (K : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        let E := B.execute f hf T hT X
        ∀ z : E.Choices, let Y := E.finalState z
          K * (X.positions + processorCount b n + Y.positions * B.growthConstant^T + Y.totalWidth)
            + 1 < min (2 ^ wordBits b n) ((processorCount b n)^2) := by
  let p := 2*(b+2)
  have hb' : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  have hθ : 0 < (u.θ : ℝ) := Rat.cast_pos.mpr u.theta_pos
  have hg : 1 ≤ (B.growthConstant : ℝ) := by
    exact_mod_cast (show 1 ≤ B.growthConstant by linarith [B.growthConstant_ge_two])
  filter_upwards [eventually_pairBranchBounds B u b hb,
    eventually_pairWorkspaceFits b hb' (K*(2*p+2)) 2 2,
    eventually_pairWorkspace_lt_square b ((le_max_right _ _).trans hb) (K*(2*p+2)),
    eventually_ge_atTop 2] with n h hfit hsquare hn
  intro base lanes labels hD hT A _ f hf X T E z Y
  have hbranch := h.2.2 labels hD hT A f hf z
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hn1' : 1 ≤ n := by omega
  have hfrac {x : ℝ} (hx : x ≤ 1) : (n : ℝ)^x ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 hx
  have hG : B.growthConstant ^ T ≤ n := by
    have h := (history_pow_blockCount_le hg hθ.le hn1' u.growth).trans (hfrac (by norm_num))
    exact_mod_cast h
  let R := processorCount b n
  let L := (n.log2+1)^2
  have hp : initialPositions b n ≤ p*R*n*L := by
    have h₀ := initialPositions_bound b n hn
    have h₁ := hfrac (by norm_num : (3/4 : ℝ) ≤ 1)
    have h₂ : (initialPositions b n : ℝ) ≤
        2*((b : ℝ)+2)*(processorCount b n : ℝ)*n*((n.log2 : ℝ)+1)^2 := by
      exact h₀.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ (by positivity))
        (sq_nonneg _))
    dsimp only [p, R, L]
    exact_mod_cast h₂
  have hw : Y.totalWidth ≤ R*n := by
    have h := hbranch.2.1.trans
      (mul_le_mul_of_nonneg_left (hfrac (by linarith)) (Nat.cast_nonneg _))
    exact_mod_cast h
  have hx := pairInput_positions S labels hD
  change X.positions = initialPositions b n at hx
  have hl : 1 ≤ L := Nat.one_le_pow _ _ (Nat.succ_pos _)
  let scale := R*n^2*L
  have hRn : R*n ≤ scale := by
    dsimp [scale]
    exact (Nat.mul_le_mul_left R (by nlinarith only [hn1'])).trans (Nat.le_mul_of_pos_right _ hl)
  have hR : R ≤ scale := (Nat.le_mul_of_pos_right _ hn1').trans hRn
  have hP : initialPositions b n ≤ p*scale := by
    apply hp.trans
    dsimp [scale]
    rw [pow_two]
    nlinarith only [Nat.le_mul_of_pos_right (p*R*n*L) hn1']
  have hhist : Y.positions * B.growthConstant ^ T ≤ p*scale := by
    exact (Nat.mul_le_mul (hbranch.1.trans hp) hG).trans_eq (by dsimp [scale]; ring)
  have ht : X.positions + R + Y.positions * B.growthConstant^T + Y.totalWidth ≤ (2*p+2)*scale := by
    rw [hx]; nlinarith only [hP,hR,hhist,hw.trans hRn]
  apply lt_of_le_of_lt _ (lt_min hfit hsquare)
  change K * (X.positions + R + Y.positions * B.growthConstant ^ T + Y.totalWidth) + 1 ≤
    K*(2*p+2)*R*n^2*L + 1
  exact Nat.add_le_add_right ((Nat.mul_le_mul_left K ht).trans_eq (by dsimp [scale]; ring)) 1

/-- The arena bound in the native word-address format. -/
theorem eventually_pairArenaFits {k : Type*} [Field k] {S : BlockSchedule k}
    (B : S.Templates) (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    (K : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        let E := B.execute f hf T hT X
        ∀ z : E.Choices, let Y := E.finalState z
          K * (X.positions + processorCount b n + Y.positions * B.growthConstant^T + Y.totalWidth)
            + 1 < 2 ^ wordBits b n := by
  filter_upwards [eventually_pairArenaFitBoth B u b hb K] with n h
  intro base lanes labels hD hT A _ f hf X T E z Y
  exact (h labels hD hT A f hf z).trans_le (min_le_left _ _)

end CursorNetwork

end VPVNP
end Computability
end OAI
