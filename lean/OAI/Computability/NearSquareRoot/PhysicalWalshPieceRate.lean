import OAI.Computability.NearSquareRoot.PhysicalWalshPieceBudget

/-! # Sparse-width bounds for the physical even-piece sweep

Every bank scan is charged at its digit multiplicity. The stage clocks, the
reused arena, the polynomial controller setup and the final store all enter
the same estimates as in the physical program.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open Filter Finset

private theorem eventually_poly (d : ℕ) : ∀ᶠ k : ℕ in atTop, (k:ℝ)^d ≤ (2:ℝ)^k := by
  filter_upwards [WalshPadding.eventually_pow_le_two_pow_half d] with k hk
  exact_mod_cast hk.trans (Nat.pow_le_pow_right (by decide) (Nat.div_le_self k 2))

private theorem volume_le {A W k s w : ℕ} {R : ℝ} (hk : (1:ℝ) ≤ k) (ww : (w:ℝ) ≤ R*k)
    (extentBound : (extent A W k s : ℝ) ≤ 2*(2:ℝ)^k) :
    sweepVolume A W k s w ≤ (2*(R+1))*((2:ℝ)^k*k) := by
  unfold sweepVolume
  calc
    _ ≤ (2*(2:ℝ)^k)*((R+1)*k) := mul_le_mul extentBound (by linarith) (by positivity) (by positivity)
    _ = _ := by ring

/-- The compact header and the greatest visited address both fit this space
bound, including the one-cell reserve for a sequential call. -/
theorem eventually_sweepSpaceRate {A W C d q : ℕ} {c R Q g : ℝ} {P : ℕ → ℝ}
    (hA : 1 < A) (hW : 0 < W) (hc : 0 ≤ c) (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hg : 0 < g) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ᶠ k : ℕ in atTop, ∀ s w : ℕ,
      (s:ℝ) ≤ g*k/Real.log (2+k) → (w:ℝ) ≤ R*k → 0 ≤ P w → P w ≤ Q*(k:ℝ)^q →
      (sweepSpace A W c P C d k s w:ℝ)+1 ≤ S*(2:ℝ)^k*k := by
  let D := (C:ℝ)*(R+3)^d
  let M := (8*(R+2)+1)+(4*c*(R+1)+2*Q)
  refine ⟨D+M+1,by dsimp [D,M]; positivity,?_⟩
  filter_upwards [eventually_poly d, eventually_poly q, WalshPadding.eventually_twice_selected_le g hg,
    WalshPadding.eventually_paddedRows_bound hA hW g hg, eventually_ge_atTop 1] with k hpd hpq small pad hk
  intro s w ss ww hP PQ
  let X := (2:ℝ)^k*k
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num) (n := k)
  have X1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le hk2 hk'
  have powX : (2:ℝ)^k ≤ X := le_mul_of_one_le_right (by positivity) hk'
  have sk : (s:ℝ) ≤ k := by exact_mod_cast (show s ≤ k by have := small s ss; omega)
  have e : (extent A W k s:ℝ) ≤ 2*(2:ℝ)^k := by exact_mod_cast (pad s ss).2.2.2.2
  have hv := volume_le hk' ww e
  have poly : (C:ℝ)*((k:ℝ)+s+w+1)^d ≤ D*X := by
    dsimp only [D]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg C)
    calc
      _ ≤ ((R+3)*k)^d := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = (R+3)^d*(k:ℝ)^d := mul_pow ..
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpd.trans powX) (by positivity)
  have raw : (extent A W k s:ℝ)*(4*((w:ℝ)+1)+4)+1 ≤ (8*(R+2)+1)*X := by
    have a := mul_le_mul e (show 4*((w:ℝ)+1)+4 ≤ (4*(R+2))*k by linarith)
      (show 0 ≤ 4*((w:ℝ)+1)+4 by positivity) (show 0 ≤ 2*(2:ℝ)^k by positivity)
    dsimp only [X] at X1 ⊢
    linarith only [a,X1]
  have recursive : 2*c*sweepVolume A W k s w+((s:ℝ)+1)*P w ≤ (4*c*(R+1)+2*Q)*X := by
    have v := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2*c by positivity)
    have setup := mul_le_mul (show (s:ℝ)+1 ≤ 2*k by linarith)
      (PQ.trans (mul_le_mul_of_nonneg_left hpq hQ)) hP (show 0 ≤ (2:ℝ)*k by positivity)
    dsimp only [X]
    linarith only [v,setup]
  have G : (sweepArena A W c P k s w:ℝ) ≤ M*X := by
    rw [sweepArena, Nat.cast_max]
    apply max_le
    · push_cast
      have h : 8*(R+2)+1 ≤ M := le_add_of_nonneg_right (by positivity)
      simpa only [extent, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        raw.trans (mul_le_mul_of_nonneg_right h (zero_le_one.trans X1))
    · have pos : 0 ≤ sweepVolume A W k s w := by unfold sweepVolume; positivity
      apply (Nat.floor_le (by positivity)).trans
      have h : 4*c*(R+1)+2*Q ≤ M := le_add_of_nonneg_left (by positivity)
      exact recursive.trans (mul_le_mul_of_nonneg_right h (zero_le_one.trans X1))
  unfold sweepSpace
  push_cast
  dsimp only [X] at poly G X1
  linarith only [poly,G,X1]

private theorem digit_clock {A calls s : ℕ} {ρ D M P G : ℝ} (hA : 1 < A) (hρ : 0 < ρ)
    (hm : 0 ≤ M) (hp : 0 ≤ P) (hg : 0 ≤ G) (t : ℕ → ℝ)
    (ht : ∀ j, t j ≤ M*((2:ℝ)*(A:ℝ)^j)^ρ+P*(calls+1:ℝ)^j)
    (digi : (∑ j : Fin (walshPieceDigits A s).length,
      ((walshPieceDigits A s).get j:ℝ)*((2:ℝ)*(A:ℝ)^(j:ℕ))^ρ) ≤ D*(s:ℝ)^ρ) :
    (∑ j : Fin (walshPieceDigits A s).length,
      ((walshPieceDigits A s).get j:ℝ)*(t j+G)) ≤ (M+G)*(D*(s:ℝ)^ρ)+P*(s:ℝ)^(calls+1) := by
  let m (j : Fin (walshPieceDigits A s).length) : ℝ := (walshPieceDigits A s).get j
  let wt (j : ℕ) := ((2:ℝ)*(A:ℝ)^j)^ρ
  have a1 : (1:ℝ) ≤ A := by exact_mod_cast hA.le
  have wt1 (j) : 1 ≤ wt j := Real.one_le_rpow (by nlinarith [one_le_pow₀ a1 (n := j)]) hρ.le
  calc
    _ ≤ ∑ j, m j*((M+G)*wt j+P*(calls+1:ℝ)^(j:ℕ)) := by
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have g := le_mul_of_one_le_right hg (wt1 j)
      have h : t j ≤ M*wt j +P*(calls+1:ℝ)^(j:ℕ) := ht j
      linarith only [h,g]
    _ = (M+G)*(∑ j, m j*wt j)+P*(∑ j, m j*(calls+1:ℝ)^(j:ℕ)) := by
      rw [mul_sum,mul_sum,←sum_add_distrib]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left digi (by positivity))
      (mul_le_mul_of_nonneg_left (walsh_piece_setup_bound hA calls s) hp)

/-- Time and space of the compiled sweep, uniform in the active field and the
record width. The linear scans between two recursive pieces are included for
each repetition in the emitted digit list. -/
theorem eventually_sweepRate {A W calls C d q : ℕ} {ρ B c H R Q g : ℝ} {L P : ℕ → ℝ}
    (hA : 1 < A) (hW : 0 < W) (hρ : 0 < ρ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hg : 0 < g) :
    ∃ T S : ℝ, 0 ≤ T ∧ 0 ≤ S ∧ ∀ᶠ k : ℕ in atTop, ∀ s w : ℕ,
      (s:ℝ) ≤ g*k/Real.log (2+k) → (w:ℝ) ≤ R*k → 0 ≤ L w → L w ≤ H*(1+Real.log (2+k)) →
      0 ≤ P w → P w ≤ Q*(k:ℝ)^q →
      (sweepTime A W calls ρ B c L P C d k s w:ℝ) ≤ T*(2:ℝ)^k*k*(1+(k:ℝ))^ρ*(1+Real.log (2+k)) ∧
      (sweepSpace A W c P C d k s w:ℝ) ≤ S*(2:ℝ)^k*k := by
  obtain ⟨S,hS,arena⟩ := eventually_sweepSpaceRate (C := C) (d := d) (q := q) (P := P) hA hW hc hR hQ hg
  obtain ⟨D,hD,digits⟩ := walsh_piece_cost_bound hA hρ
  let E := B*H*(2*(R+1))
  refine ⟨2*S+(E+S)*D+Q,S,by dsimp [E]; positivity,hS,?_⟩
  filter_upwards [arena,eventually_poly (q+(calls+1)),WalshPadding.eventually_paddedRows_bound hA hW g hg,
    WalshPadding.eventually_twice_selected_le g hg,eventually_ge_atTop 1] with k room poly pad small hk
  intro s w ss ww hL LH hP PQ
  let X := (2:ℝ)^k*k
  let F := (1+(k:ℝ))^ρ
  let Z := 1+Real.log (2+(k:ℝ))
  let G := sweepSpace A W c P C d k s w
  let V := sweepVolume A W k s w
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have X0 : 0 ≤ X := by dsimp [X]; positivity
  have F1 : 1 ≤ F := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) k]) hρ.le
  have Z1 : 1 ≤ Z := by dsimp only [Z]; linarith [Real.log_nonneg (by linarith : 1 ≤ (2+(k:ℝ)))]
  have sk : (s:ℝ) ≤ k := by exact_mod_cast (show s ≤ k by have := small s ss; omega)
  have sf : (s:ℝ)^ρ ≤ F := Real.rpow_le_rpow (by positivity) (by linarith) hρ.le
  have e : (extent A W k s:ℝ) ≤ 2*(2:ℝ)^k := by exact_mod_cast (pad s ss).2.2.2.2
  have v0 : 0 ≤ V := by dsimp [V,sweepVolume]; positivity
  have v : V ≤ (2*(R+1))*X := volume_le hk' ww e
  have hG : (G:ℝ)+1 ≤ S*X := by simpa only [mul_assoc,X,G] using room s w ss ww hP PQ
  refine ⟨?_,by change (G:ℝ) ≤ S*(2:ℝ)^k*k; rw [mul_assoc]; exact (le_add_of_nonneg_right zero_le_one).trans hG⟩
  have localC (j : ℕ) : (stageClock A W calls ρ B L P k s w j:ℝ) ≤
      B*L w*V*((2:ℝ)*(A:ℝ)^j)^ρ + P w*(calls+1:ℝ)^j := Nat.floor_le (by positivity)
  have exactSum := digit_clock hA hρ (M := B*L w*V) (P := P w) (G := (G:ℝ)+1)
    (by positivity) hP (by positivity) _ localC (digits s)
  have LV : B*L w*V ≤ E*(X*Z) := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left LH hB) v v0 (show 0 ≤ B*(H*(1+Real.log (2+k))) by
      change 0 ≤ B*(H*Z)
      exact mul_nonneg hB (mul_nonneg hH (zero_le_one.trans Z1)))
    dsimp only [E,Z]
    linarith only [h]
  have XZ : X ≤ X*Z := le_mul_of_one_le_right X0 Z1
  have param := add_le_add LV (hG.trans (mul_le_mul_of_nonneg_left XZ hS))
  have hull : B*L w*V +((G:ℝ)+1) ≤ (E+S)*(X*Z) := by linarith only [param]
  let Y := X*F*Z
  have XleY : X ≤ Y := (le_mul_of_one_le_right X0 F1).trans
    (le_mul_of_one_le_right (mul_nonneg X0 (zero_le_one.trans F1)) Z1)
  have pq : P w*(s:ℝ)^(calls+1) ≤ Q*(2:ℝ)^k := by
    have ss' := pow_le_pow_left₀ (Nat.cast_nonneg s) sk (calls+1)
    have h := mul_le_mul PQ ss' (by positivity) (show 0 ≤ Q*(k:ℝ)^q by positivity)
    exact h.trans (by rw [mul_assoc,←pow_add]; exact mul_le_mul_of_nonneg_left poly hQ)
  have setup := pq.trans (mul_le_mul_of_nonneg_left
    ((le_mul_of_one_le_right (show 0 ≤ (2:ℝ)^k by positivity) hk').trans XleY) hQ)
  have inner := mul_le_mul hull (mul_le_mul_of_nonneg_left sf hD) (by positivity)
    (show 0 ≤ (E+S)*(X*Z) by dsimp [E]; positivity)
  have castTime : (sweepTime A W calls ρ B c L P C d k s w:ℝ) = 2*((G:ℝ)+1) +
      ∑ j : Fin (walshPieceDigits A s).length, ((walshPieceDigits A s).get j:ℝ)*
        ((stageClock A W calls ρ B L P k s w j:ℝ)+((G:ℝ)+1)) := by
    simp only [sweepTime,G,Nat.cast_sum,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,add_assoc]
  rw [castTime]
  have lead := mul_le_mul_of_nonneg_left (hG.trans (mul_le_mul_of_nonneg_left XleY hS)) (show (0:ℝ)≤2 by norm_num)
  change _ ≤ (2*S+(E+S)*D+Q)*(2:ℝ)^k*k*F*Z
  dsimp only [Y,X] at exactSum setup inner lead ⊢
  linarith only [exactSum,setup,inner,lead]

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
