import OAI.Computability.NearSquareRoot.PhysicalWalshXorGate
import OAI.Computability.NearSquareRoot.PhysicalWalshXorThresholdLog

/-! # Thresholds for the interior three-field XOR

A single active field on each side of the three native fields pays for
the polynomial table reserve and the sublinear row-interpreter factor.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorThreshold

open IntegerMultiplication IntegerMultiplication.Strip NearSquareRoot.Controlled
open XorReserve

/-- The row-interpreter exponent acts on the three-field window. -/
noncomputable def factor (ρ : ℝ) (L : ℕ) := ⌈2*((3*L+1 : ℕ):ℝ)^ρ⌉₊

def cutoff (D Q : ℕ) := max 6 (payloadBits D Q)

theorem factor_pays {I : Type} (ρ : ℝ) (L : I → ℕ) (i : I) :
    2*Spindle.modes (fun j => 3*L j) (τ:=ρ) i ≤ factor ρ (L i) := Nat.le_ceil _

private theorem linear_le_pow {L : ℕ} (six : 6 ≤ L) : 2*(3*L+1) ≤ 2^L := by
  induction L, six using Nat.le_induction with
  | base => decide
  | succ L _ ih => rw [pow_succ]; omega

theorem factor_le_prefix {ρ : ℝ} (upper : ρ ≤ 1) {D Q L P : ℕ}
    (large : cutoff D Q ≤ L) (prefixFits : L ≤ P) : factor ρ L ≤ 2^P := by
  have six := (le_max_left _ _).trans large
  have one : (1:ℝ) ≤ ((3*L+1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ 3*L+1 by omega)
  have grow := Real.rpow_le_rpow_of_exponent_le one upper
  rw [Real.rpow_one] at grow
  apply Nat.ceil_le.mpr
  calc
    2*((3*L+1 : ℕ):ℝ)^ρ ≤ 2*((3*L+1 : ℕ):ℝ) := mul_le_mul_of_nonneg_left grow (by norm_num)
    _ ≤ (2^P : ℕ) := by exact_mod_cast (linear_le_pow six).trans (Nat.pow_le_pow_right (by decide) prefixFits)

theorem payload_le_suffix {D Q L A : ℕ} (arity : 5 ≤ A) (large : cutoff D Q ≤ L) :
    payloadBits D Q ≤ (A-4)*L :=
  ((le_max_right _ _).trans large).trans (Nat.le_mul_of_pos_left _ (by omega))

theorem factor_rate {ρ : ℝ} (lower : 0 ≤ ρ) (upper : ρ ≤ 1) {L : ℕ} (pos : 0 < L) :
    (factor ρ L+1 : ℕ) ≤ 8*(1+(L:ℝ)^ρ) := by
  have base : ((3*L+1 : ℕ):ℝ) ≤ 4*(L:ℝ) := by exact_mod_cast (show 3*L+1 ≤ 4*L by omega)
  have scale := Real.rpow_le_rpow (by positivity) base lower
  rw [Real.mul_rpow (by norm_num) (by positivity)] at scale
  have four := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) upper
  rw [Real.rpow_one] at four
  have fit := scale.trans (mul_le_mul_of_nonneg_right four (Real.rpow_nonneg (Nat.cast_nonneg L) _))
  have ceil := (Nat.ceil_lt_add_one (show 0 ≤ 2*((3*L+1 : ℕ):ℝ)^ρ by positivity)).le
  unfold factor
  push_cast
  push_cast at fit ceil
  linarith only [fit,ceil]

/-- Below the large-window threshold, one elementary scan per bit requires
only logarithmically many scans in the controller scale. -/
theorem small_scans {D Q L : ℕ} (largeScale : 2 ≤ Q) (small : L < cutoff D Q) :
    (L:ℝ) ≤ (6+172*(D:ℝ))*(1+Real.log (2+Q)) := by
  have z : 0 ≤ Real.log (2+(Q:ℝ)) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) Q])
  have h : Nat.clog 2 (Q+1) ≤ 4+3*guardWidth (3*Q) := by
    have mono := Nat.clog_mono_right 2 (show Q+1 ≤ 3*Q+1 by omega)
    unfold guardWidth
    omega
  have cap : (Nat.clog 2 (Q+1):ℝ) ≤ 172*(1+Real.log (2+Q)) :=
    (show (Nat.clog 2 (Q+1):ℝ) ≤ ((4+3*guardWidth (3*Q):ℕ):ℝ) by exact_mod_cast h).trans (passes_log le_rfl largeScale)
  have hL : (L:ℝ) ≤ cutoff D Q := by exact_mod_cast small.le
  apply hL.trans
  simp only [cutoff,Nat.cast_max,payloadBits,Nat.cast_mul,Nat.cast_ofNat,max_le_iff]
  have times := mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg (α:=ℝ) D)
  have pos := mul_nonneg (Nat.cast_nonneg (α:=ℝ) D) (add_nonneg zero_le_one z)
  constructor <;> nlinarith only [times,pos,z]

/-- Exact clock emitted by the bounded gate interpreter. -/
noncomputable def gateClock (ρ : ℝ) (L V : ℕ) :=
  (4+3*guardWidth (3*L))*(V*(factor ρ L+1))+1

theorem clock_rate {ρ : ℝ} (lower : 0 ≤ ρ) (upper : ρ ≤ 1) {L Q : ℕ}
    (positive : 0 < L) (fit : L ≤ Q) (large : 2 ≤ Q) (V : ℕ) :
    (gateClock ρ L V : ℝ) ≤ 1376*(1+Real.log (2+Q))*V*(1+(L:ℝ)^ρ)+1 := by
  have ratio := mul_le_mul_of_nonneg_left (factor_rate lower upper positive) (Nat.cast_nonneg (α:=ℝ) V)
  have nonneg : 0 ≤ Real.log (2+(Q:ℝ)) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) Q])
  have stages := mul_le_mul (passes_log fit large) ratio (by positivity) (by positivity)
  unfold gateClock
  push_cast at stages ⊢
  linarith only [stages]

/-- Once the table degree is chosen, a large-field call to the physical XOR
only needs one prefix field and the low fields beyond the scratch slot. -/
theorem boundedGateLarge {ρ : ℝ} (lower : 1/2 < ρ) (upper : ρ ≤ 1)
    {A : ℕ} (arity : 5 ≤ A) {X : Type} {r : Regime X} (P L : X → ℕ)
    (hP : IntegerMultiplication.Staff.Realizes r P) (hL : IntegerMultiplication.Staff.Realizes r L)
    {U : X → Type} (u : (x:X) → Series (U x)) :
    ∃ D : ℕ, ∀ {Y : Type} (select : Y → X) (m Q : Y → ℕ),
      (∀ y, (u (select y)).count = pack ((A-4)*L (select y)) (m y)) →
      (∀ y, r.scale (select y) ≤ Q y) → (∀ y, 0 < m y) →
      (∀ y, cutoff D (Q y) ≤ L (select y)) → (∀ y, L (select y) ≤ P (select y)) →
      let V y := volume (P (select y)) (3*L (select y)) ((A-4)*L (select y)) (m y)
      let T := (y:Y) × XorWindow.Input (P (select y)) (3*L (select y)) (U (select y))
      Space.BoundedTask (fun t:T => gateClock ρ (L (select t.1)) (V t.1)) (fun t => V t.1)
        (fun t => .fork (r.header (select t.1)) (XorWindow.store (u (select t.1)) t.2))
        (fun t => XorWindow.store (u (select t.1)) (t.2 ∘ Controlled.PositionProgram.directed (XorSweep.gate (L (select t.1))))) := by
  have h3 := (IntegerMultiplication.Staff.Realizes.fix 3).times hL
  obtain ⟨D,run⟩ := XorWindow.boundedGateOn lower P (fun x => 3*L x) hP h3 u
  refine ⟨D,fun select m Q lengths scale pos big high => ?_⟩
  have gate := run select (fun y => (A-4)*L (select y)) m Q (fun y => factor ρ (L (select y)))
    lengths scale pos (fun y => payload_le_suffix arity (big y)) (fun y => factor_pays ρ L (select y))
    (fun y => factor_le_prefix upper (big y) (high y))
  simpa only [Nat.mul_div_cancel_left _ (by decide : 0 < 3),gateClock] using gate

end PhysicalWalsh.XorThreshold

end NearSquareRoot
end Computability
end OAI
