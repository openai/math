import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSelector
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # A computable reserve independent of the native interpreter degree

When a field exceeds the square of the descriptor logarithm, its payload
absorbs every fixed polynomial up to a template-dependent constant. That
constant enlarges only the resource estimate and adds no bits to the tape.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorSquare
open IntegerMultiplication Code Strip Staff Carry Space Controlled XorThreshold XorReserve PhysicalWalshNode

def cut (Q : ℕ) := (Nat.clog 2 (Q+1))^2
def threshold (Q : ℕ) := max 6 (cut Q)
def guard (L Q : ℕ) := min L (cut Q)

theorem threshold_eq (Q : ℕ) : threshold Q = cutoff (Nat.clog 2 (Q+1)) Q := by
  simp [threshold,cut,cutoff,payloadBits,pow_two]

theorem reserve_slack (D Q : ℕ) : payloadBits D Q ≤ cut Q+D^2 := by
  let z := Nat.clog 2 (Q+1)
  change D*z ≤ z^2+D^2
  rcases le_total D z with h | h
  · exact (Nat.mul_le_mul_right z h).trans (by rw [←sq]; omega)
  · exact (Nat.mul_le_mul_left D h).trans (by rw [←sq]; omega)

theorem reserve_le_extra {D Q B : ℕ} (room : cut Q ≤ B) : payloadBits D Q ≤ B+D^2 :=
  (reserve_slack D Q).trans (Nat.add_le_add_right room _)

/-- The uninflated reserve suffices once the recorded precision is large. -/
theorem reserve_le_cut {D Q : ℕ} (big : 2^D ≤ Q) : payloadBits D Q ≤ cut Q := by
  have enough := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (Nat.lt_succ_of_le big)
  exact (Nat.mul_le_mul_right _ enough.le).trans_eq (sq _).symm

theorem precision_le_scale (A : ℕ) (s : Shape) : s.w ≤ Header.scale A s := by
  rw [Header.scale_exact]; omega

theorem precision_reserve {D A : ℕ} (s : Shape) (wide : 2^D ≤ s.w) :
    payloadBits D (Header.scale A s) ≤ cut (Header.scale A s) :=
  reserve_le_cut (wide.trans (precision_le_scale A s))

theorem guard_reserve {L Q : ℕ} (active : 0 < L-guard L Q) (D : ℕ) :
    payloadBits D Q ≤ guard L Q+D^2 := by
  unfold guard at active ⊢
  by_cases h : L ≤ cut Q
  · rw [min_eq_left h,Nat.sub_self] at active; omega
  · simpa only [min_eq_right (by omega : cut Q ≤ L)] using reserve_slack D Q

theorem payload_slack {D Q B m : ℕ} (room : cut Q ≤ B) :
    2^(payloadBits D Q)*m ≤ 2^(D^2)*pack B m := by
  have le := Nat.mul_le_mul_right m (Nat.pow_le_pow_right (by decide : 0 < 2) (reserve_le_extra (D:=D) room))
  simpa only [XorReserve.pack,pow_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using le

theorem polynomial_slack {D Q B m : ℕ} (room : cut Q ≤ B) (pos : 0 < m) :
    (Q+1)^D ≤ 2^(D^2)*pack B m :=
  (payload_capacity D Q m pos).trans (payload_slack room)

/-- The selected bit cutoff can be computed by one polynomial tape program
from the descriptor, without supplying the degree as an input. -/
theorem has_cut {X : Type} {r : Regime X} {Q : X → ℕ} (scale : Figure r Q) :
    Realizes r (cut ∘ Q) := by
  have count := (scale.added (Figure.natural 1)).short_log
  simpa only [cut,Function.comp_apply,Function.comp_def,pow_two] using count.times count

theorem has_switch {X : Type} {r : Regime X} {Q L : X → ℕ} (scale : Figure r Q) (width : Realizes r L) :
    r.Has (fun x => decide (threshold (Q x) ≤ L x)) := by
  simpa only [threshold_eq] using
    FrontDispatch.hasComparison ((scale.added (Figure.natural 1)).short_log) scale width

theorem has_guard {X : Type} {r : Regime X} {Q L : X → ℕ} (scale : Figure r Q) (width : Realizes r L) :
    Realizes r (fun x => guard (L x) (Q x)) := by
  let c := cut ∘ Q
  have h : Realizes r c := has_cut scale
  have take := width.select h (width.below h)
  convert take using 1
  funext i
  change min (L i) (c i) = if L i < c i then L i else c i
  split <;> omega

/-- Inflating the costed width does not alter the physical record stream. -/
theorem virtual_volume (P k B e m : ℕ) :
    volume P k (B+e) m = 2^e*volume P k B m := by
  simp only [XorReserve.volume,pow_add]
  ring

theorem virtual_clock (ρ : ℝ) (P k B e m L : ℕ) :
    gateClock ρ L (volume P k (B+e) m)+1 ≤ (2^e+1)*(gateClock ρ L (volume P k B m)+1) := by
  rw [virtual_volume]
  dsimp only [gateClock]
  ring_nf
  omega

/-- A bound proved for a fixed extra analytic width is a bound for the
true volume with the identical command and a larger hidden constant. -/
theorem actual_runs {I : Type} {c : Cmd} (ρ : ℝ) (P k B m L : I → ℕ) (e : ℕ)
    (q r : I → Tree)
    (wide : EffectiveBoundedTask.Runs c (fun i => gateClock ρ (L i) (volume (P i) (k i) (B i+e) (m i)))
      (fun i => volume (P i) (k i) (B i+e) (m i)) q r) :
    EffectiveBoundedTask.Runs c (fun i => gateClock ρ (L i) (volume (P i) (k i) (B i) (m i)))
      (fun i => volume (P i) (k i) (B i) (m i)) q r := by
  apply wide.bound (2^e+1) (2^e+1)
  · exact fun i => virtual_clock ρ (P i) (k i) (B i) e (m i) (L i)
  · intro i; rw [virtual_volume,Nat.succ_mul,Nat.mul_add]; omega

end PhysicalWalsh.XorSquare

end NearSquareRoot
end Computability
end OAI
