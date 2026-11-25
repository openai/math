import OAI.Hierarchy.ProbeRepairGain
import OAI.Hierarchy.ProbeRepairReplayAccount
import OAI.Hierarchy.ProbeSaturatedReplayAccount
import OAI.Hierarchy.ProbeOuterLedger
import OAI.Hierarchy.ProtocolRAMAttemptThresholds

namespace OAI
/-! # The signed budget for both branches of a physical repair attempt -/

namespace Hierarchy

namespace ProtocolRAM.AttemptGate

open Computability.VPVNP.BurstRAM PrivateRAM

/-- The main mesh advances on a low excess score and, during injection,
a low payload score. Stopping is a separate test on the running account. -/
def outerLow {w : ℕ} (t : Inputs) (m : Memory w) : Bool :=
  !(bit t.excess m || (t.injection && bit t.payload m))

/-- The low predicate reads the two integer comparisons actually stored by the
three-pass threshold machine, including the earlier prefix sum under the second scan. -/
theorem TestBoard.outerLow_after {w : ℕ} (b : TestBoard) (m : Memory w) (wide : 0<w)
    (xlo : b.excess.out+b.excess.rows<b.payload.out)
    (plo : b.payload.out+b.payload.rows<b.discrepancy.out) :
    outerLow b.inputs (b.after m) =
      !(b.excess.high m || (b.injection && b.payload.high (b.excess.after m))) := by
  have keep (c : Check) (a : Memory w) (bank : Bank) (below : bank.base<c.out) :
      bit bank (c.after a) = bit bank a := by
    simp [bit, Bank.read, c.frame a _ below]
  have excessBelow : b.excess.bank.base < b.discrepancy.out := by
    change b.excess.out + b.excess.rows < b.discrepancy.out
    omega
  unfold outerLow TestBoard.inputs TestBoard.after
  simp only [keep b.discrepancy _ b.excess.bank excessBelow,
    keep _ _ _ (show b.excess.bank.base<b.payload.out from xlo),
    keep _ _ _ (show b.payload.bank.base<b.discrepancy.out from plo), Check.flag _ _ wide]

theorem actual_of_outer_high {w : ℕ} (t : Inputs) (m : Memory w)
    (main : t.reserve = false) (running : bit t.stop m = false)
    (high : outerLow t m = false) :
    actual t m = if bit t.discrepancy m then 2 else 3 := by
  have trigger : (bit t.excess m || (t.injection && bit t.payload m)) = true := by
    cases e : (bit t.excess m || (t.injection && bit t.payload m)) <;> simp_all [outerLow]
  simp [actual, selectMode, main, running, trigger]

end ProtocolRAM.AttemptGate

namespace AdaptiveProbe.OuterBank

open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM
noncomputable section

variable {I X : Type*} [Fintype I] (B : OuterBank I X)

/-- A real purchase either keeps the low-exception test on every completed
slice or exhausts its failed-repair fuel and pays all remaining integer feeds. -/
def PurchaseReadback (n w K cap : ℕ) (ρ γ ρBuy reward s : ℝ) (x out : X) : Prop :=
  Nonempty (B.ReplayRows n w K cap ρ γ ρBuy reward s x out) ∨
    Nonempty (B.SaturatedReplayRows n w K cap ρ γ ρBuy reward s x out)

theorem PurchaseReadback.decrease {n w K cap : ℕ} {ρ γ ρBuy reward s : ℝ} {x out : X}
    (receipt : B.PurchaseReadback n w K cap ρ γ ρBuy reward s x out)
    (hw : 0<w) (hK : 0<K) (hγ : 0<γ) (hρ : 0<ρ) (hρBuy : 0<ρBuy) (hr : 0<reward)
    (hn : 0<n) (ha : 0<B.a) (hb : ∀ i, 0≤B.coefficient i) (hM : 0≤B.M) (hs : 0<s)
    (s1 : s≤1) (box : ∀ i, 0≤B.box i)
    (saturates : ∀ t, 0<t → t≤1 → ∀ i, t*rowSlope B.a (B.coefficient i) B.M (B.box i)≤cap) :
    B.balance w s out ≤ B.balance w s x - (n:ℝ)*ρBuy*reward/8 := by
  rcases receipt with accurate | exhausted
  · obtain ⟨rows⟩ := accurate
    exact ReplayRows.decrease B rows hw hK hγ hρ hρBuy hr hn ha hb hM hs s1 box saturates
  · obtain ⟨rows⟩ := exhausted
    exact SaturatedReplayRows.decrease B rows hw hK hγ hρ hρBuy hr hn ha hb hM hs s1 box saturates

/-- Uniform inputs are before the branch. Each outgoing selector supplies
integer readbacks, finite reserve history and its own actual signed charges. -/
structure RepairReadbacks (n w m K cap : ℕ) (s₀ floor ρ γ ρBuy reward : ℝ)
    (good : ℕ → X → Bool) (next : ℕ → ℕ → X → X) where
  policy : ℕ → ℕ → X → AttemptGate.Inputs
  snapshot : ℕ → ℕ → X → Memory w
  main : ∀ j < m+m, ∀ h x, (policy j h x).reserve = false
  test : ∀ j < m+m, ∀ h x, AttemptGate.outerLow (policy j h x) (snapshot j h x) = good j x
  running : ∀ j < m+m, ∀ h x, good j x = false → floor < B.normalized w n m s₀ j x →
    AttemptGate.bit (policy j h x).stop (snapshot j h x) = false
  failed : ∀ j < m+m, ∀ h x, AttemptGate.actual (policy j h x) (snapshot j h x) = 2 →
    Nonempty (B.FailedRows n w K cap ρ γ (phaseTime s₀ m j) x (next j h x))
  bought : ∀ j < m+m, ∀ h x, AttemptGate.actual (policy j h x) (snapshot j h x) = 3 →
    B.PurchaseReadback n w K cap ρ γ ρBuy reward (phaseTime s₀ m j) x (next j h x)

/-- This is the `saves` premise of `outer_budget`, derived by executing its two
possible repair modes on the actual threshold words. -/
theorem RepairReadbacks.saves {n w m K cap : ℕ} {s₀ floor ρ γ ρBuy reward : ℝ}
    {good : ℕ → X → Bool} {next : ℕ → ℕ → X → X}
    (R : B.RepairReadbacks n w m K cap s₀ floor ρ γ ρBuy reward good next)
    (hn : 0<n) (hw : 0<w) (hm : 0 < m) (hK : 0<K)
    (hρ : 0<ρ) (hγ : 0<γ) (hρBuy : 0<ρBuy) (hr : 0<reward) (hs₀ : 0<s₀) (hs₁ : s₀≤1)
    (ha : 0<B.a) (hb : ∀ i, 0≤B.coefficient i) (hM : 0≤B.M) (box : ∀ i, 0≤B.box i)
    (saturates : ∀ t : ℝ, 0<t → t≤1 → ∀ i, t*rowSlope B.a (B.coefficient i) B.M (B.box i)≤cap) :
    ∀ j < m+m, ∀ h x, good j x=false → floor < B.normalized w n m s₀ j x →
      B.normalized w n m s₀ j (next j h x) + repairGain K ρ γ ρBuy reward ≤
        B.normalized w n m s₀ j x := by
  intro j hj h x bad above
  let s := phaseTime s₀ m j
  have bounds := clock_bounds hs₀ hs₁ hm (j-m) (by omega)
  have hs : 0<s := hs₀.trans_le bounds.1
  have s1 : s≤1 := bounds.2
  have mode := AttemptGate.actual_of_outer_high (R.policy j h x) (R.snapshot j h x)
    (R.main j hj h x) (R.running j hj h x bad above) ((R.test j hj h x).trans bad)
  have signed : B.balance w s (next j h x) ≤
      B.balance w s x - n * repairGain K ρ γ ρBuy reward := by
    cases disc : AttemptGate.bit (R.policy j h x).discrepancy (R.snapshot j h x) with
    | false =>
      have picked := R.bought j hj h x (by simpa only [disc, Bool.false_eq_true, ite_false] using mode)
      have budget := PurchaseReadback.decrease B picked hw hK hγ hρ hρBuy hr hn ha hb hM hs s1 box saturates
      have gain := mul_le_mul_of_nonneg_left (min_le_right (ρ*γ/(8*K)) (ρBuy*reward/8))
        (Nat.cast_nonneg (α:=ℝ) n)
      refine budget.trans (sub_le_sub_left ?_ _)
      exact gain.trans_eq (by ring)
    | true =>
      have picked := R.failed j hj h x (by simpa only [disc, ite_true] using mode)
      obtain ⟨record⟩ := picked
      have budget := FailedRows.decrease B record hw hK hγ ha hb hM hs box (saturates s hs s1)
      have gain := mul_le_mul_of_nonneg_left (min_le_left (ρ*γ/(8*K)) (ρBuy*reward/8))
        (Nat.cast_nonneg (α:=ℝ) n)
      refine budget.trans (sub_le_sub_left ?_ _)
      exact gain.trans_eq (by ring)
  have np : 0 < (n:ℝ) := by exact_mod_cast hn
  change B.balance w s (next j h x) / n + _ ≤ B.balance w s x / n
  apply (le_div_iff₀ np).2
  rw [add_mul, div_mul_cancel₀ _ np.ne']
  linarith only [signed]

/-- The observed attempts supply a single positive fuel rate, independent of
the word width, site count, phase, and outgoing selector. The signed terminal
balance includes every catalyst credit and all payments for routed spills. -/
theorem outer_budget_of_readbacks {n w m K cap : ℕ} {s₀ r scale V G C D ρ γ ρBuy reward : ℝ}
    (hn : 0<n) (hm : 0 < m) (hw : m≤w) (hK : 0<K)
    (hρ : 0<ρ) (hγ : 0<γ) (hρBuy : 0<ρBuy) (hrw : 0<reward)
    (hs : 0<s₀) (hs₁ : s₀≤1) (hr : 0<r) (hr₁ : r≤1)
    (sc : 0≤ scale) (intg : scale*(1-Real.log r)≤1)
    (hV : 0≤V) (hG : 0≤G) (hC : 0≤C) (hD : 0≤D)
    (lv : V≤B.a*m) (lg : G≤ s₀*B.a*m) (bound : OuterBounds B n w m cap s₀ V G C D)
    (move : ℕ→X→X) (events : B.Caps m w cap move) (start : X)
    (startPrice : B.balance w 1 start≤n) (endScore : s₀*score B.a B.M B.coefficient B.box≤n)
    (good : ℕ→X→Bool) (next : ℕ→ℕ→X→X)
    (payloadLow : ∀ j < m, ∀ x, good j x=true → pairing (fun i=>(B.payload i:ℝ))
      (maximizer B.a B.M 1 B.coefficient B.box (B.units w x))≤(3/2:ℝ)*n)
    (coolLow : ∀ j < m, ∀ x, good (m+j) x=true → score B.a B.M B.coefficient
      (maximizer B.a B.M (clockTime s₀ m j) B.coefficient B.box (B.units w x))≤
        (scale*min (1/clockTime s₀ m j) (1/r)+1/2)*n)
    (receipts : B.RepairReadbacks n w m K cap s₀ (-(C+D+1)) ρ γ ρBuy reward good next) :
    ∀ fuel : ℕ, 5-(fuel:ℝ)*repairGain K ρ γ ρBuy reward≤ -(C+D+1) →
      let final := (outerRun next good (B.normalized w n m s₀) (-(C+D+1)) fuel move start (m+m)).1
      B.cash final + pairing (B.units w final) B.box ≤ 6*n := by
  have gain := repairGain_pos hK hρ hγ hρBuy hrw
  exact B.outer_budget hn hm hw hs hs₁ hr hr₁ sc intg hV hG hC hD gain lv lg bound
    move events start startPrice endScore good next payloadLow coolLow
    (RepairReadbacks.saves B receipts hn (hm.trans_le hw) hm hK hρ hγ hρBuy hrw hs hs₁
      bound.aPos bound.bNonneg bound.MNonneg bound.boxNonneg bound.capBound)


end
end AdaptiveProbe.OuterBank
end Hierarchy

end OAI
