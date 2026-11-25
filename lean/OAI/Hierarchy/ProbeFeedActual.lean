import OAI.Hierarchy.ProbeLedger
import OAI.Hierarchy.ProbeFeed

namespace OAI
/-! # Feeding the withheld integer inventory along the actual nonlinear ledger -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

variable {I : Type*} [Fintype I]

/-- The normalized bit increment read from the integer reserve tape at one fixed tick. -/
def reserveDelta (w m j : ℕ) (bits : I → ℕ) (i : I) : ℝ :=
  (slice m (bits i-bits i/2) j:ℝ)/w

omit [Fintype I] in
theorem reserveDelta_error {w m j : ℕ} (bits : I → ℕ) (hw : 0 < w) (hm : 0 < m) (i : I) :
    |reserveDelta w m j bits i-((bits i:ℝ)/w)/(2*m)| ≤ 2/(w:ℝ) := by
  have h := (reserve_slices m (bits i) hm).2 j
  have wpos : (0:ℝ) < w := by exact_mod_cast hw
  rw [reserveDelta,show ((bits i:ℝ)/w)/(2*m)=((bits i:ℝ)/(2*m))/w by ring,←sub_div,abs_div,abs_of_pos wpos]
  exact div_le_div_of_nonneg_right h wpos.le

/-- This tick uses the actual pre-feed inventory after any preceding repairs. Account
changes from those repairs are already negative. The two terms of the remainder are
the true rounding and curvature charges. -/
theorem real_feed_tick {a M t s : ℝ} (b A z : I → ℝ) (bits : I → ℕ) {w m j : ℕ}
    (hw : 0 < w) (hm : 0 < m) (room : m ≤ w) (ha : 0 < a) (hb : ∀ i, 0 ≤ b i)
    (hM : 0 ≤ M) (hs : 0 < s) (s1 : s ≤ 1) (half : s/2 ≤ t)
    (hz : ∀ i, 0 ≤ z i) (hA : ∀ i, 0 ≤ A i) {Z G cap : ℝ}
    (hZ : 0 ≤ Z) (hG : 0 ≤ G) (caps : ∀ i, A i ≤ cap)
    (bounded : ∀ i, (bits i:ℝ)/w ≤ Z) :
    let dt := s/(2*m)
    let δ := reserveDelta w m j bits
    let x := maximizer a M t b A z
    (∀ i, |rowSlope a (b i) M (x i)| ≤ G) →
    potential a M (t+dt) b A (fun i => z i+δ i) ≤ potential a M t b A z +
      dt*(pairing (fun i => (bits i:ℝ)/w) x/s-score a M b x) +
      Fintype.card I*(2*cap/w + ((Z+2+G)/m)^2/(2*s*a)) := by
  intro dt δ x slopes
  have realW : (0:ℝ) < w := by exact_mod_cast hw
  have realM : (0:ℝ) < m := by exact_mod_cast hm
  have mw : (m:ℝ) ≤ w := by exact_mod_cast room
  have ht : 0 < t := by linarith
  have hdt : 0 < dt := by dsimp [dt]; positivity
  have δpos (i : I) : 0 ≤ δ i := by dsimp [δ,reserveDelta]; positivity
  have xt (i : I) : x i ∈ Set.Icc 0 (A i) := (offer_spec ha (hb i) hM ht (hz i) (hA i)).1
  have small (i : I) := reserveDelta_error (j:=j) bits hw hm i
  have round (i : I) : δ i*x i ≤ ((bits i:ℝ)/w)/(2*m)*x i+2*cap/w := by
    have delta := (abs_le.mp (small i)).2
    change δ i-_ ≤ _ at delta
    have via := mul_le_mul_of_nonneg_right delta (xt i).1
    have cap' := mul_le_mul_of_nonneg_left ((xt i).2.trans (caps i)) (show 0 ≤ 2/(w:ℝ) by positivity)
    rw [sub_mul] at via
    calc
      δ i*x i ≤ ((bits i:ℝ)/w)/(2*m)*x i + (2/(w:ℝ))*cap := by linarith only [via,cap']
      _ = _ := by ring
  have boundδ (i : I) : δ i ≤ (Z+2)/m := by
    have hi := (abs_le.mp (small i)).2
    change δ i-_ ≤ _ at hi
    have inv := div_le_div_of_nonneg_left (show 0 ≤ (2:ℝ) by norm_num) realM mw
    have cap' := div_le_div_of_nonneg_right (bounded i) (show 0 ≤ 2*(m:ℝ) by positivity)
    have coarse : Z/(2*m) ≤ Z/m := div_le_div_of_nonneg_left hZ realM (by linarith)
    rw [add_div]; linarith
  have curve (i : I) : (δ i-dt*rowSlope a (b i) M (x i))^2/(4*(t+dt)*a) ≤
      ((Z+2+G)/m)^2/(2*s*a) := by
    have clock : dt ≤ 1/(m:ℝ) := by
      dsimp [dt]; apply (div_le_div_iff₀ (by positivity : 0 < 2*(m:ℝ)) realM).2
      nlinarith only [mul_le_mul_of_nonneg_right s1 realM.le,realM.le]
    have term := mul_le_mul clock (slopes i) (abs_nonneg _) (by positivity)
    have mag := abs_add_le (δ i) (-(dt*rowSlope a (b i) M (x i)))
    rw [←sub_eq_add_neg,abs_neg,abs_of_nonneg (δpos i),abs_mul,abs_of_pos hdt] at mag
    have full : |δ i-dt*rowSlope a (b i) M (x i)| ≤ (Z+2+G)/m := by
      exact (mag.trans (add_le_add (boundδ i) term)).trans_eq (by ring)
    have squares := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (Z+2+G)/(m:ℝ))).2 full
    apply (div_le_div_of_nonneg_right (by simpa using squares) (by positivity : 0 ≤ 4*(t+dt)*a)).trans
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right half ha.le,mul_nonneg hdt.le ha.le]
  have drift := Finset.sum_le_sum (s:=Finset.univ) fun i _ => round i
  have bend := Finset.sum_le_sum (s:=Finset.univ) fun i _ => curve i
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at drift bend
  have exactdrift : (∑ i, ((bits i:ℝ)/w)/(2*m)*x i) = dt*(pairing (fun i => (bits i:ℝ)/w) x/s) := by
    dsimp [dt,pairing]
    rw [Finset.sum_div,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; field_simp [hs.ne',realM.ne',realW.ne']
  rw [exactdrift] at drift
  have inc := potential_increment (s:=t) (s':=t+dt) b A z δ ha hb hM ht (add_pos ht hdt)
    hz (fun i => add_nonneg (hz i) (δpos i)) hA
  rw [add_sub_cancel_left] at inc
  change _ ≤ potential a M t b A z+pairing δ x-dt*score a M b x+_ at inc
  change pairing δ x ≤ _ at drift
  nlinarith only [inc,drift,bend]

/-- A single mesh works for all population sizes and all sufficiently wide physical
words. The rounding term decays with w while the time/stock curvature decays with m. -/
theorem choose_feed_mesh {L cap C a s ζ : ℝ} (_hL : 0 ≤ L) (hc : 0 ≤ cap) (ha : 0 < a)
    (hs : 0 < s) (hz : 0 < ζ) : ∃ m : ℕ, 0 < m ∧ ∃ w₀ : ℕ, m ≤ w₀ ∧
      ∀ (w n : ℕ), w₀ ≤ w → (Fintype.card I:ℝ) ≤ L*n →
      (m:ℝ)*((Fintype.card I:ℝ)*(2*cap/w+(C/m)^2/(2*s*a))) ≤ (n:ℝ)*ζ/2 := by
  obtain ⟨m,many⟩ := exists_nat_gt (max (2*L*C^2/(s*a*ζ)) 0)
  have hm : 0 < (m:ℝ) := (le_max_right ..).trans_lt many
  obtain ⟨w₀,wide⟩ := exists_nat_gt (max (8*(m:ℝ)*L*cap/ζ) m)
  have enough := (le_max_left ..).trans_lt many
  have broad := (le_max_left ..).trans_lt wide
  have room : (m:ℝ) ≤ w₀ := ((le_max_right ..).trans_lt wide).le
  refine ⟨m,by exact_mod_cast hm,w₀,by exact_mod_cast room,?_⟩
  intro w n hw dim
  have wbound : (w₀:ℝ) ≤ w := by exact_mod_cast hw
  have wpos := hm.trans_le (room.trans wbound)
  have first : (m:ℝ)*L*(2*cap/w) ≤ ζ/4 := by
    have q := (div_lt_iff₀ hz).mp (broad.trans_le wbound)
    rw [←mul_div_assoc,div_le_div_iff₀ wpos (by norm_num : (0:ℝ)<4)]
    nlinarith only [q.le]
  have second : (m:ℝ)*L*((C/m)^2/(2*s*a)) ≤ ζ/4 := by
    have q := (div_lt_iff₀ (show 0 < s*a*ζ by positivity)).mp enough
    have src : (m:ℝ)*L*((C/m)^2/(2*s*a))=(L*C^2)/(2*s*a*m) := by
      field_simp [hm.ne',hs.ne',ha.ne']
    rw [src,div_le_div_iff₀ (show 0 < 2*s*a*(m:ℝ) by positivity) (by norm_num : (0:ℝ)<4)]
    nlinarith only [q.le]
  have scalar := add_le_add first second
  have monotone := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right dim
    (show 0 ≤ 2*cap/(w:ℝ)+(C/m)^2/(2*s*a) by positivity)) hm.le
  nlinarith only [monotone,mul_le_mul_of_nonneg_left scalar (Nat.cast_nonneg (α:=ℝ) n)]

/-- Splice every finite native replacement history into the actual integer reserve
replay. The two ledger receipts are local chronological obligations: pre-tick repairs
save cash plus the old potential, and post-tick capping spends precisely the released
potential. The numerical rate and quadratic/rounding costs are proved here. -/
theorem purchased_replay {a M s cap Z G fee saved cash : ℝ}
    (b A : I → ℝ) (bits : I → ℕ) {w m : ℕ} (hw : 0 < w) (hm : 0 < m) (room : m ≤ w)
    (ha : 0 < a) (hb : ∀ i, 0 ≤ b i) (hM : 0 ≤ M) (hs : 0 < s) (s1 : s ≤ 1)
    (hA : ∀ i, 0 ≤ A i) (hZ : 0 ≤ Z) (hG : 0 ≤ G)
    (caps : ∀ i, A i ≤ cap) (bounded : ∀ i, (bits i:ℝ)/w ≤ Z)
    (pre : ℕ → I → ℝ) (cashAfterRepair account : ℕ → ℝ) :
    let z := fun i => (bits i:ℝ)/w
    let dt := s/(2*m)
    let t := fun j : ℕ => s/2+j*dt
    let x := fun j => maximizer a M (t j) b A (pre j)
    (∀ j < m, ∀ i, 0 ≤ pre j i) →
    (∀ j < m, ∀ i, |rowSlope a (b i) M (x j i)| ≤ G) →
    (∀ j < m, 2*(fee+saved) ≤ s*divergence a M b (maximizer a M s b A z) (x j)) →
    (account 0 ≤ cash+fee+potential a M (s/2) b A (fun i => ((bits i/2:ℕ):ℝ)/w)) →
    (∀ j < m, cashAfterRepair j+potential a M (t j) b A (pre j) ≤ account j) →
    (∀ j < m, account (j+1) ≤ cashAfterRepair j + potential a M (t (j+1)) b A
      (fun i => pre j i+reserveDelta w m j bits i)) →
    (m:ℝ)*(Fintype.card I*(2*cap/w+((Z+2+G)/m)^2/(2*s*a))) ≤ saved/2 →
    account m ≤ cash+potential a M s b A z-saved/2 := by
  intro z dt t x nonneg grad bought initial repair capTick loss
  have dtpos : 0 < dt := by dsimp [dt]; positivity
  have half (j : ℕ) : s/2 ≤ t j := le_add_of_nonneg_right (by positivity)
  have tick (j : ℕ) : t (j+1)=t j+dt := by dsimp [t]; push_cast; ring
  let err := (Fintype.card I:ℝ)*(2*cap/w+((Z+2+G)/m)^2/(2*s*a))
  apply finite_purchase b A z ha hb hM hs (fun i => by dsimp [z]; positivity) hA m hm x account
    (fun _ => err) cash fee saved
  · intro j hj i
    exact (offer_spec ha (hb i) hM (by linarith [half j]) (nonneg j hj i) (hA i)).1
  · exact bought
  · have start := split_start b A bits w hw ha hb hM hs hA
    have halfCost := potential_half b A z ha hb hM hs (fun i => by dsimp [z]; positivity) hA
    linarith
  · intro j hj
    have bnd := real_feed_tick (j:=j) b A (pre j) bits hw hm room ha hb hM hs s1 (half j)
      (nonneg j hj) hA hZ hG caps bounded (grad j hj)
    have end' := capTick j hj
    rw [tick] at end'
    change potential a M (t j+dt) b A _ ≤ potential a M (t j) b A (pre j)+
      dt*(pairing z (x j)/s-score a M b (x j))+err at bnd
    change _ ≤ account j+dt*(pairing z (x j)/s-score a M b (x j))+err
    linarith only [bnd,end',repair j hj]
  · simpa [err] using loss

end
end Hierarchy.AdaptiveProbe

end OAI
