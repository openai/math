import OAI.Hierarchy.ProbeStrictActivation
import OAI.Hierarchy.ProbeRetainedRows
import OAI.Hierarchy.ProbeStripThreshold
import OAI.Hierarchy.ProtocolRAMCalendarThreshold

namespace OAI
/-! # A genuine reserve advance supplies the post-purchase discrepancy payment -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage AttemptGate PurchaseStage
open scoped BigOperators Classical
noncomputable section

variable {w q e : ℕ} (C : Chart w q e) (mem : Memory w) (p h j b : ℕ)

def replayCheck := (repair C (.inner p h j b)).tests.discrepancy

def replayScoreMemory :=
  let a := Attempt.inner p h j b
  let B := repair C a
  let m := prepared C a (innerState C mem p h j b)
  B.tests.payload.after (B.tests.excess.after m)

theorem passed_replay_check (room : TestRoom (repair C (.inner p h j b)) w)
    (advance : observedInnerMode C mem p h j b=1) :
    (∑i,(replayCheck C p h j b).score (replayScoreMemory C mem p h j b) i)<(replayCheck C p h j b).bound := by
  let a := Attempt.inner p h j b
  let B := repair C a
  let m := prepared C a (innerState C mem p h j b)
  have yes : B.tests.discrepancy.high (B.tests.payload.after (B.tests.excess.after m))=false :=
    (discrepancy_votes (C.layout a) B m room).2 (.inr ⟨rfl,advance⟩)
  exact lt_of_not_ge (of_decide_eq_false yes)

/-- Every retained chain has a distinct physical candidate row. All other word
scores are nonnegative, so their number does not enter the rounding allowance. -/
theorem passed_replay_sum {P : Type*} [Fintype P] {n Q N : ℕ} {ε ρ : ℝ}
    (he : 0<ε) (hρ : 0<ρ) (hQ : 0<Q) (size : Fintype.card P≤n)
    (room : TestRoom (repair C (.inner p h j b)) w) (advance : observedInnerMode C mem p h j b=1)
    (threshold : (replayCheck C p h j b).bound=⌈4*failureTolerance N ε ρ*n*Q⌉₊)
    (pick : P ↪ Fin (replayCheck C p h j b).rows) (actual : P→ℝ)
    (read : ∀path,actual path≤((replayCheck C p h j b).score (replayScoreMemory C mem p h j b) (pick path):ℝ)/Q+
      failureTolerance N ε ρ) : (∑path,actual path)≤(ρ*n/4)*ε := by
  have measured := passed_replay_check C mem p h j b room advance
  rw [threshold] at measured
  have low := Nat.lt_ceil.mp measured
  rw [Nat.cast_sum] at low
  have params := failure_tolerance (N:=N) he hρ
  calc (∑path,actual path) ≤ _ := StripDirectory.sum_retained pick _ actual params.1.le hQ size read low
       _ ≤ ρ*n*ε/4 := (params.2 n).2
       _ = _ := by ring

/-- At a real advance opcode, the native sum on the selected candidate tape
charges all bought probes and the fixed strict saving, including exceptional strips. -/
theorem acquired_payment {F : Type*} [Field F] {z d k depth J Q N : ℕ} {M η ε : ℝ}
    (payment : StrictPayment F depth k M η ε) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (marked : StageAt z d→(Fin k×Bool)→Finset (Fin (2^z)))
    (unique : ∀t c c' r,r∈marked t c → r∈marked t c'→c=c') (stages : (permutationFabric z d).shapes.length≤depth+1)
    (global : ColumnSite (StageColumns z d) k ↪ Fin J) (a s B u δ fee ρ : ℝ)
    (old post : Commodity (Fin (2^z)) (permutationFabric z d).shapes.length k→ℝ)
    (ha : 0≤a) (hs : 0 ≤ s) (s₁ : s≤1) (hB : 0<B) (hu : 0<u) (hρ : 0<ρ) (δu : 4*δ^2≤u)
    (res : η<δ) (long : 1+η<(depth+1:ℕ)*(δ-η))
    (eligible : ∀t c r,r∈marked t c→u ≤ s*(rise M (old (.inr ((r,t),c))))^2)
    (box : ∀path v,0≤postQuote S π depth marked path post v ∧ postQuote S π depth marked path post v≤M+1)
    (many : ρ*(2^z:ℕ)≤Fintype.card (LiveChains S π depth marked)) (cheap : fee≤(B*u/8)/2)
    (he : 0<ε) (hQ : 0<Q) (space : TestRoom (repair C (.inner p h j b)) w) (advance : observedInnerMode C mem p h j b=1)
    (threshold : (replayCheck C p h j b).bound=⌈4*failureTolerance N ε ρ*(2^z:ℕ)*Q⌉₊)
    (pick : LiveChains S π depth marked ↪ Fin (replayCheck C p h j b).rows)
    (read : ∀path, ChainStrip.namedError F depth k (namedStrip S π depth marked global path).name M
      (postQuote S π depth marked path post) ≤ ((replayCheck C p h j b).score
        (replayScoreMemory C mem p h j b) (pick path):ℝ)/Q+failureTolerance N ε ρ) :
    2*((Fintype.card (LiveChains S π depth marked):ℝ)*fee+(2^z:ℕ)*ρ*(B*u/8)/4)≤
      s*divergence a M (bonus B) old post := by
  refine (payment S π marked global a s B u δ fee ρ old post ha hs s₁ hB hu hρ δu res long eligible box many cheap ?_).2
  exact passed_replay_sum C mem p h j b he hρ hQ (purchased_card_le S π depth marked unique stages)
    space advance threshold pick _ read

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
