import OAI.Hierarchy.ProbeRepairHistogramAccount
import OAI.Hierarchy.ProbeFeedActual

namespace OAI
/-! # The purchased reserve replay on the physical outer bank -/

namespace Hierarchy.AdaptiveProbe.OuterBank

open scoped BigOperators
noncomputable section

variable {I X : Type*} [Fintype I] (B : OuterBank I X)

/-- Time at the entrance to the repairs preceding the next reserve slice. -/
def replayTime (s : ℝ) (m j : ℕ) : ℝ := s/2 + j*(s/(2*m))

/-- Integer stock immediately after delivery of the current reserve slice, before
routing any bits in excess of the physical cap. -/
def replayFeed (m j : ℕ) (x pre : X) (i : I) : ℕ :=
  B.stock pre i + slice m (B.stock x i - B.stock x i/2) j

private theorem replayTime_end (s : ℝ) {m : ℕ} (hm : 0 < m) : replayTime s m m = s := by
  unfold replayTime
  field_simp [Nat.cast_ne_zero.mpr hm.ne']; ring

private theorem replayTime_bounds {s : ℝ} {m j : ℕ} (hs : 0 < s) (hm : 0 < m) (hj : j ≤ m) :
    0 < replayTime s m j ∧ replayTime s m j ≤ s := by
  have dt : 0 ≤ s/(2*(m:ℝ)) := by positivity
  refine ⟨by unfold replayTime; positivity, ?_⟩
  calc
    replayTime s m j ≤ replayTime s m m :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) dt)
    _ = s := replayTime_end s hm

/-- The observed states of one purchase, including its inner repair attempts and
the whole-bit stocks before and after every delivery. The activation receipt is
evaluated on the actual post-repair price at each tick. -/
structure ReplayRows (n w K cap : ℕ) (ρ γ ρBuy reward s : ℝ) (x out : X) where
  m : ℕ
  mesh_pos : 0 < m
  mesh_fits : m ≤ w
  states : ℕ → ℕ → X
  attempts : ℕ → ℕ
  bought : ℕ
  fee : ℝ
  boxMax : ℝ
  box_bound : ∀ i, B.box i ≤ boxMax
  entry_fits : ∀ i, B.stock x i ≤ cap*w
  initial_cash : B.cash (states 0 0) ≤ B.cash x + bought*fee
  initial_stock : ∀ i, B.stock (states 0 0) i = B.stock x i/2
  terminal : states m 0 = out
  repairs : ∀ j < m, ∀ k < attempts j,
    Nonempty (B.FailedRows n w K cap ρ γ (replayTime s m j) (states j k) (states j (k+1))) ∨
    (B.cash (states j (k+1)) = B.cash (states j k) ∧ B.stock (states j (k+1)) = B.stock (states j k))
  retained : ∀ j < m, ∀ i, B.stock (states (j+1) 0) i =
    min (B.replayFeed m j x (states j (attempts j)) i) (cap*w)
  charged : ∀ j < m, B.cash (states (j+1) 0) ≤ B.cash (states j (attempts j)) +
    pairing (bitStock w (spillBits cap w (B.replayFeed m j x (states j (attempts j))))) B.box
  activation : ∀ j < m, 2*((bought:ℝ)*fee+(n:ℝ)*ρBuy*reward/4) ≤ s*divergence B.a B.M B.coefficient
    (maximizer B.a B.M s B.coefficient B.box (B.units w x))
    (maximizer B.a B.M (replayTime s m j) B.coefficient B.box (B.units w (states j (attempts j))))
  mesh_error : (m:ℝ)*(Fintype.card I*(2*boxMax/w+(((cap:ℝ)+2+cap)/m)^2/(2*s*B.a))) ≤
    (n:ℝ)*ρBuy*reward/8

/-- The reserve replay pays for every purchased probe, including the exceptional
ones. Intermediate failed attempts, clipped feeds, and the purchase debit are
all evaluated on the observed chronological states. -/
theorem ReplayRows.decrease {n w K cap : ℕ} {ρ γ ρBuy reward s : ℝ} {x out : X}
    (H : B.ReplayRows n w K cap ρ γ ρBuy reward s x out) (hw : 0 < w) (hK : 0 < K)
    (hγ : 0 < γ) (hρ : 0 < ρ) (_hρBuy : 0 < ρBuy) (_hr : 0 < reward) (hn : 0 < n)
    (ha : 0 < B.a) (hb : ∀ i, 0 ≤ B.coefficient i) (hM : 0 ≤ B.M) (hs : 0 < s) (s1 : s ≤ 1)
    (box : ∀ i, 0 ≤ B.box i)
    (saturates : ∀ t, 0 < t → t ≤ 1 → ∀ i, t*rowSlope B.a (B.coefficient i) B.M (B.box i) ≤ cap) :
    B.balance w s out ≤ B.balance w s x - (n:ℝ)*ρBuy*reward/8 := by
  let pre := fun j => H.states j (H.attempts j)
  let time := replayTime s H.m
  let account := fun j => B.balance w (time j) (H.states j 0)
  have bounds (j : ℕ) (hj : j ≤ H.m) : 0 < time j ∧ time j ≤ 1 :=
    let h := replayTime_bounds hs H.mesh_pos hj
    ⟨h.1,h.2.trans s1⟩
  have repair (j : ℕ) (hj : j < H.m) : B.balance w (time j) (pre j) ≤ account j := by
    have chain (k : ℕ) (hk : k ≤ H.attempts j) :
        B.balance w (time j) (H.states j k) ≤ account j := by
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        refine le_trans ?_ (ih (by omega))
        rcases H.repairs j hj k (by omega) with failed | ⟨cash,stock⟩
        · have ht := bounds j hj.le
          have drop := FailedRows.decrease B (Classical.choice failed) hw hK hγ ha hb hM ht.1 box (saturates _ ht.1 ht.2)
          exact drop.trans (sub_le_self _ (by positivity))
        · have same : B.units w (H.states j (k+1)) = B.units w (H.states j k) := by
            funext i
            change ((B.stock (H.states j (k+1)) i:ℝ)/w) = (B.stock (H.states j k) i:ℝ)/w
            rw [stock]
          simpa only [balance,cash,same] using (le_refl (B.balance w (time j) (H.states j k)))
    exact chain (H.attempts j) le_rfl
  have positive (j : ℕ) (i : I) : 0 ≤ B.units w (pre j) i := by unfold units; positivity
  have capSlope (i : I) : rowSlope B.a (B.coefficient i) B.M (B.box i) ≤ cap := by
    simpa only [one_mul] using saturates 1 zero_lt_one le_rfl i
  have grad (j : ℕ) (hj : j < H.m) :=
    (outer_gradient_box B.coefficient B.box (B.units w (pre j)) cap ha hb hM
      (bounds j hj.le).1 (positive j) box capSlope).2.1
  have initial : account 0 ≤ B.cash x + H.bought*H.fee +
      potential B.a B.M (s/2) B.coefficient B.box (fun i => ((B.stock x i/2:ℕ):ℝ)/w) := by
    have stock : B.units w (H.states 0 0) = fun i => ((B.stock x i/2:ℕ):ℝ)/w := by
      funext i; simp only [units,H.initial_stock]
    simpa only [account,time,balance,replayTime,Nat.cast_zero,zero_mul,add_zero,stock] using
      (add_le_add H.initial_cash (le_refl
        (potential B.a B.M (s/2) B.coefficient B.box (B.units w (H.states 0 0)))))
  have feed (j : ℕ) (hj : j < H.m) : account (j+1) ≤ B.cash (pre j) +
      potential B.a B.M (time (j+1)) B.coefficient B.box
        (fun i => B.units w (pre j) i + reserveDelta w H.m j (B.stock x) i) := by
    have ht := bounds (j+1) (by omega)
    have pay := B.capped_balance (H.states (j+1) 0) (B.replayFeed H.m j x (pre j))
      (B.cash (pre j)) hw ha hb hM ht.1 (saturates _ ht.1 ht.2) (H.retained j hj) (H.charged j hj)
    have raw : bitStock w (B.replayFeed H.m j x (pre j)) =
        fun i => B.units w (pre j) i + reserveDelta w H.m j (B.stock x) i := by
      funext i
      simp only [bitStock,replayFeed,Nat.cast_add,add_div,units,reserveDelta]
    rw [raw] at pay
    exact pay
  have bounded (i : I) : (B.stock x i:ℝ)/w ≤ cap :=
    (div_le_iff₀ (Nat.cast_pos.mpr hw)).2 (by exact_mod_cast H.entry_fits i)
  have replay := purchased_replay (cap:=H.boxMax) (Z:=(cap:ℝ)) (G:=(cap:ℝ)) (fee:=(H.bought:ℝ)*H.fee)
    (saved:=(n:ℝ)*ρBuy*reward/4) (cash:=B.cash x) B.coefficient B.box (B.stock x) hw H.mesh_pos
    H.mesh_fits ha hb hM hs s1 box (Nat.cast_nonneg _) (Nat.cast_nonneg _) H.box_bound bounded
    (fun j => B.units w (pre j)) (fun j => B.cash (pre j)) account
    (fun j _ => positive j) grad H.activation initial repair feed (by linarith only [H.mesh_error])
  change B.balance w (replayTime s H.m H.m) (H.states H.m 0) ≤ B.balance w s x - _ at replay
  rw [replayTime_end s H.mesh_pos,H.terminal] at replay
  linarith only [replay]


end
end Hierarchy.AdaptiveProbe.OuterBank

end OAI
