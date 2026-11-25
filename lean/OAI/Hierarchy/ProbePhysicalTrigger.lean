import OAI.Hierarchy.ProbeObservedTrigger
import OAI.Hierarchy.ProbeObservedReplay
import OAI.Hierarchy.ProbePublicCalibration
import OAI.Hierarchy.ProbeNativeTrigger

namespace OAI
/-! # Observed outer purchase forces motion at the same public calibration as reserve payments -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage AttemptGate PurchaseStage
open scoped BigOperators Classical
noncomputable section

variable {w q d : ℕ} (C : Chart w q d) (mem : Memory w) (p h : ℕ)

def outerCheck := (repair C (.outer p h)).tests.discrepancy

def outerScoreMemory :=
  let a := Attempt.outer p h
  let B := repair C a
  let m := prepared C a (trialState C mem p h)
  B.tests.payload.after (B.tests.excess.after m)

theorem purchased_payload_check (space : TestRoom (repair C (.outer p h)) w)
    (purchase : observedMode C mem p h=3) :
    (∑i,(outerCheck C p h).score (outerScoreMemory C mem p h) i)<(outerCheck C p h).bound := by
  let a := Attempt.outer p h
  let B := repair C a
  let m := prepared C a (trialState C mem p h)
  have yes : B.tests.discrepancy.high (B.tests.payload.after (B.tests.excess.after m))=false :=
    (discrepancy_votes (C.layout a) B m space).2 (.inl purchase)
  exact lt_of_not_ge (of_decide_eq_false yes)

private theorem inverse_gap {W : ℕ} (wide : 9≤W) : 2*(W:ℝ)⁻¹^4≤(W:ℝ)⁻¹^2 := by
  have big : (9:ℝ)≤W := by exact_mod_cast wide
  have pos : 0<(W:ℝ) := by linarith
  simp only [←one_div]
  field_simp
  nlinarith [sq_nonneg ((W:ℝ)-9),mul_nonneg (show 0≤(W:ℝ)-9 by linarith) pos.le,
    mul_nonneg (show 0≤(W:ℝ)^2-2 by nlinarith) (sq_nonneg (W:ℝ))]

/-- The public cutoff is shared by the two score tests. The inner/outer names can
differ at every row. A purchased decision reads a low local discrepancy sum and
one of the actual high score/payload bills from the native program. -/
theorem physical_trigger_of_votes {F : Type*} [Field F] {z k W M Q : ℕ} {u σ Λ ε : ℝ}
    (cfg : PublicCalibration F k u σ Λ W M ε) (space : TestRoom (repair C (.outer p h)) w)
    (purchase : observedMode C mem p h=3) (hQ : 0<Q) (a s : ℝ) (hs : 0<s) (s₁ : s≤1) :
    let N := publicStages W
    let T := probeHeat W
    let n : ℕ := 2^z
    let r := (dyadicScale W)^8
    let cutoff := failureTolerance N ε (probeDensity k W)
    let check := outerCheck C p h
    ∀ (x : Commodity (Fin n) N k→ℝ) (name : Fin n→PayloadStrip.Naming N k),
    a*(∑i,(x i)^2)/n≤(W:ℝ)⁻¹^4 → (∀i,PayloadStrip.rowQuotes x i∈Set.Icc 0 (PayloadStrip.ceiling N k M)) →
    check.bound=⌈4*cutoff*n*Q⌉₊ → ∀pick : Fin n ↪ Fin check.rows,
    (∀ i,PayloadStrip.namedError F N k (name i) M (PayloadStrip.rowQuotes x i) ≤
      (check.score (outerScoreMemory C mem p h) (pick i):ℝ)/Q+cutoff) →
    (envelope W r s < score a M (bonus (probeBonus W)) x/n ∨
      (s=1 ∧ (n:ℝ)<∑i,x (.inl i))) →
    (Fintype.card (Fin n×Fin N):ℝ)≤∑ v,∑ j : Fin k×Bool,s*(rise M (x (.inr (v,j)))/T)^2 := by
  intro N T n r cutoff check x name quad box threshold pick read high
  have stages : 0<N := Nat.succ_pos _
  have rp : 0<r := by dsimp [r,dyadicScale]; positivity
  have temp : 0<T := by dsimp [T,probeHeat,dyadicScale]; positivity
  have np : 0<(n:ℝ) := by dsimp [n]; positivity
  have low := purchased_payload_check C mem p h space purchase
  change (∑i,check.score (outerScoreMemory C mem p h) i)<check.bound at low
  rw [threshold] at low
  have raw := Nat.lt_ceil.mp low
  rw [Nat.cast_sum] at raw
  have total := StripDirectory.sum_retained (n:=n) pick _ _ cfg.cutoff.1.le hQ (by simp) read raw
  have small := total.trans ((cfg.cutoff.2 n).1)
  apply trigger_motion (W:=(W:ℝ)) (a:=a) (r:=r) x hs s₁ rp temp stages
    (by simpa only [Fintype.card_fin] using quad) (inverse_gap ((le_max_left ..).trans cfg.wide)) _ cfg.early _
    (by
      have coeff : (W:ℝ)⁻¹^4 / ((N:ℝ)*T^2) = probeBonus W := rfl
      simpa only [Fintype.card_fin,coeff] using high)
  · rintro ⟨⟨i,t⟩,axis⟩
    have bounded := (box i).2 (.inr (t,axis))
    change x (.inr ((i,t),axis))≤M+1 at bounded
    exact max_le (by linarith) zero_le_one
  · intro energy
    exact cfg.payload (Fin n) name x box energy (by simpa only [Fintype.card_fin] using small)

private abbrev calibratedVotes (C : Chart w q d) (mem : Memory w) (p h : ℕ)
    (n : ℕ) (barrier score payload : ℝ) (conclusion : Prop) : Prop :=
  let a := Attempt.outer p h
  let B := repair C a
  let m := prepared C a (trialState C mem p h)
  ∀ (c b : ℝ) (X : SumCalibration B.tests.excess m score c)
    (Y : SumCalibration B.tests.payload (B.tests.excess.after m) payload b),
    X.threshold=n*(barrier+3/8) → Y.threshold=n*(1+3/8) → conclusion

/-- Both global vote calibrations at their chronological score memories suffice. -/
theorem physical_trigger {F : Type*} [Field F] {z k W M Q : ℕ} {u σ Λ ε : ℝ}
    (cfg : PublicCalibration F k u σ Λ W M ε) (space : TestRoom (repair C (.outer p h)) w)
    (purchase : observedMode C mem p h=3) (hQ : 0<Q) (a s : ℝ) (hs : 0<s) (s₁ : s≤1)
    (injection : p<C.mesh.inject → s=1) :
    let N := publicStages W
    let T := probeHeat W
    let n : ℕ := 2^z
    let r := (dyadicScale W)^8
    let cutoff := failureTolerance N ε (probeDensity k W)
    let check := outerCheck C p h
    ∀ (x : Commodity (Fin n) N k→ℝ) (name : Fin n→PayloadStrip.Naming N k),
    a*(∑i,(x i)^2)/n≤(W:ℝ)⁻¹^4 → (∀i,PayloadStrip.rowQuotes x i∈Set.Icc 0 (PayloadStrip.ceiling N k M)) →
    check.bound=⌈4*cutoff*n*Q⌉₊ → ∀pick : Fin n ↪ Fin check.rows,
    (∀ i,PayloadStrip.namedError F N k (name i) M (PayloadStrip.rowQuotes x i) ≤
      (check.score (outerScoreMemory C mem p h) (pick i):ℝ)/Q+cutoff) →
    calibratedVotes C mem p h n (envelope W r s) (score a M (bonus (probeBonus W)) x)
      (∑ i : Fin n, x (.inl i))
      ((Fintype.card (Fin n×Fin N):ℝ)≤∑ v,∑ j : Fin k×Bool,s*(rise M (x (.inr (v,j)))/T)^2) := by
  intro N T n r cutoff check x name quad box threshold pick read
  dsimp only [calibratedVotes]
  intro c b X Y xc yc
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.two_pow_pos z)
  exact physical_trigger_of_votes C mem p h cfg space purchase hQ a s hs s₁ x name quad box threshold pick read
    (observed_excess C mem p h space purchase n (envelope W r s) s _ _ c b np injection X Y xc yc)

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
