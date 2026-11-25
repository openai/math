import OAI.Hierarchy.GridDyadicScale
import OAI.Hierarchy.UniversalTick

namespace OAI
/-! # The rounded evaluator clock and block count for the programmed grid -/

namespace Hierarchy.GridScale

open Filter
open scoped Topology

/-- Cost before rounding to the next dyadic cap. -/
def evalWork (w k A c a q : ℕ) := (side a)^k * pairs A w q * (w+1)^c

def evalDepth (w k A c a q : ℕ) := (evalWork w k A c a q).log2 + 1

def traceBlocks (k a : ℕ) := (20*k+32)*a

theorem cap_round (w k A c a q : ℕ) (positive : 0 < evalWork w k A c a q) :
    evalWork w k A c a q ≤ 2^evalDepth w k A c a q ∧
    2^evalDepth w k A c a q ≤ 2*evalWork w k A c a q := by
  refine ⟨Nat.lt_log2_self.le, ?_⟩
  unfold evalDepth
  rw [pow_succ, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.log2_self_le positive.ne')

/-- The depth of the true rounded cap lies within a fixed multiple of the
common sublinear overhead from the volume exponent, uniformly for all ticks. -/
theorem depth_range {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (k A c : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0 < q → q ≤ Q w → let a := overhead Q D w
      w ≤ evalDepth w k A c a q + a ∧ evalDepth w k A c a q ≤ w+(10*k+3)*a := by
  filter_upwards [bounds H, sublinear H 1, polynomial H 1 A, polynomial H 1 c,
    (grows H).eventually_ge_atTop 1, eventually_ge_atTop 1] with w b aw pa pc apos wp
  intro q hq top
  let a := overhead Q D w
  have aw' : a ≤ w := by simpa [a] using aw
  change 1 ≤ a at apos
  have pa' : w^A ≤ 2^a := (Nat.pow_le_pow_left (Nat.le_succ w) A).trans (by simpa [a] using pa)
  have pc' : (w+1)^c ≤ 2^a := by simpa [a] using pc
  have B := pairs_bounds A aw' wp pa' hq (top.trans b.1)
  let work := evalWork w k A c a q
  have low : 2^(w-a) ≤ work := by
    apply B.1.trans
    change _ ≤ (side a)^k * pairs A w q * (w+1)^c
    exact (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by exact Nat.two_pow_pos (10*a)))).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos w)))
  have high : work ≤ 2^(w+(10*k+2)*a) := by
    calc
      work ≤ (2^(10*a))^k * 2^(w+a) * 2^a := Nat.mul_le_mul (Nat.mul_le_mul_left _ B.2) pc'
      _ = _ := by rw [←pow_mul,←pow_add,←pow_add]; congr 1; ring
  have positive : work ≠ 0 := ne_of_gt ((Nat.two_pow_pos _).trans_le low)
  have loDepth := (Nat.le_log2 positive).mpr low
  have pow := (Nat.log2_self_le positive).trans high
  have hiDepth : work.log2 ≤ w+(10*k+2)*a := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp pow
  change w ≤ work.log2+1+a ∧ work.log2+1 ≤ w+(10*k+3)*a
  have extra : (10*k+3)*a = (10*k+2)*a+a := by ring
  rw [extra]
  omega

/-- The compressor receives an admissible pair of scales for the very same
rounded evaluator cap and the chosen public block count. -/
theorem trace_scale {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (k A c : ℕ)
    (q : ℕ → ℕ) (range : ∀ᶠ w : ℕ in atTop, 0 < q w ∧ q w ≤ Q w) :
    TraceDistribution.Scale (fun w => evalDepth w k A c (overhead Q D w) (q w))
      (fun w => traceBlocks k (overhead Q D w)) := by
  constructor
  · apply tendsto_order.mpr
    constructor
    · intro t ht
      filter_upwards [real_sublinear H 1 (half_pos (sub_pos.mpr ht)),depth_range H k A c,
        range,eventually_ge_atTop 1] with w small depth qgood hw
      have pos : (0:ℝ)<w := by exact_mod_cast (show 0 < w by omega)
      have lb := (depth _ qgood.1 qgood.2).1
      have bound : (w:ℝ) ≤ evalDepth w k A c (overhead Q D w) (q w) + (overhead Q D w : ℝ) := by exact_mod_cast lb
      apply (lt_div_iff₀ pos).2
      nlinarith only [small,bound,mul_pos (sub_pos.mpr ht) pos]
    · intro t ht
      filter_upwards [real_sublinear H (10*k+3) (half_pos (sub_pos.mpr ht)),depth_range H k A c,
        range,eventually_ge_atTop 1] with w small depth qgood hw
      have pos : (0:ℝ)<w := by exact_mod_cast (show 0 < w by omega)
      have hb := (depth _ qgood.1 qgood.2).2
      have bound : (evalDepth w k A c (overhead Q D w) (q w) : ℝ) ≤
          w + ((10*k+3:ℕ):ℝ)*(overhead Q D w:ℝ) := by exact_mod_cast hb
      apply (div_lt_iff₀ pos).2
      nlinarith only [bound,small,mul_pos (sub_pos.mpr ht) pos]
  · apply tendsto_order.mpr
    constructor
    · intro t ht
      filter_upwards with w using ht.trans_le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    · intro t ht
      filter_upwards [real_sublinear H (20*k+32) (half_pos ht),eventually_ge_atTop 1] with w small hw
      have pos : (0:ℝ)<w := by exact_mod_cast (show 0 < w by omega)
      apply (div_lt_iff₀ pos).2
      change ((traceBlocks k (overhead Q D w) : ℕ):ℝ) < _
      rw [traceBlocks,Nat.cast_mul]
      nlinarith only [small,mul_pos ht pos]

/-- Dividing the total wire volume by 2^s leaves room for every fixed power
of the word size in the genuine selector length. -/
theorem shared_room {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (k A c e : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0 < q → q ≤ Q w → let a := overhead Q D w
      2^evalDepth w k A c a q * (w+1)^e ≤ selector k w a * 2^traceBlocks k a := by
  filter_upwards [depth_range H k A c, polynomial H 1 e,sublinear H (10*k+24)] with w d poly small
  intro q hq top
  let a := overhead Q D w
  have pow : (w+1)^e ≤ 2^a := by simpa [a] using poly
  have high := (d _ hq top).2
  change 2^(evalDepth w k A c a q) * (w+1)^e ≤ 2^(w-(10*k+24)*a)*2^((20*k+32)*a)
  calc
    _ ≤ 2^(w+(10*k+3)*a)*2^a := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) high) pow
    _ ≤ _ := by
      rw [← pow_add,← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      have equal : (20*k+32)*a = (10*k+24)*a+(10*k+3)*a+5*a := by ring
      rw [equal]
      change (10*k+24)*a ≤ w at small
      omega

/-- Both variable-length fields and the leading branch flag fit in the very
same selector word string. The wire bound is multiplied through by the actual
block denominator, avoiding any rounding assumption about the wire count. -/
theorem selector_room {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (k A c e C : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → let a := overhead Q D w
      ∀ records wires : ℕ, records≤2^(3*w/5) →
      wires*2^traceBlocks k a ≤ C*2^evalDepth w k A c a q*(w+1)^e →
      1+records+wires ≤ selector k w a := by
  filter_upwards [shared_room H k A c (e+1),sublinear H (10*(10*k+24)),
    eventually_ge_atTop (max 20 (2*C))] with w shared small age
  intro q hq top a records wires recordBound wireBound
  have slack : 2*(2^(3*w/5)+1) ≤ selector k w a := by
    have narrow : 3*w/5+2≤w-(10*k+24)*a := by
      change 10*(10*k+24)*a≤w at small
      rw [Nat.mul_assoc] at small
      omega
    have pow := Nat.pow_le_pow_right (by decide : 0<2) narrow
    change _≤2^(w-(10*k+24)*a)
    calc
      _ ≤ 2^(3*w/5+2) := by rw [pow_add]; have := Nat.two_pow_pos (3*w/5); omega
      _ ≤ _ := pow
  have fee : (2*C)*(w+1)^e ≤ (w+1)^(e+1) := by
    rw [pow_succ,Nat.mul_comm ((w+1)^e)]
    exact Nat.mul_le_mul_right _ (by omega)
  have available := shared q hq top
  change 2^evalDepth w k A c a q*(w+1)^(e+1) ≤ selector k w a*2^traceBlocks k a at available
  have bound : (2*wires)*2^traceBlocks k a ≤ selector k w a*2^traceBlocks k a := by
    calc
      _ = 2*(wires*2^traceBlocks k a) := by ring
      _ ≤ 2*(C*2^evalDepth w k A c a q*(w+1)^e) := Nat.mul_le_mul_left _ wireBound
      _ = 2^evalDepth w k A c a q*((2*C)*(w+1)^e) := by ring
      _ ≤ _ := (Nat.mul_le_mul_left _ fee).trans available
  have wireRoom := Nat.le_of_mul_le_mul_right bound (Nat.two_pow_pos _)
  omega

/-- The true weighted-trace work allowance divided by the number of physical
ticks is little-oh of the actual programmed tick clock.  An arbitrary fixed
integer factor is absorbed at the strict exponent inequality. -/
theorem average_work {Q : ℕ → ℕ} {D : ℕ → ℝ} (_env : Envelopes Q D)
    (k A c₁ c₂ C : ℕ) (saving : UniversalTick.saving+c₁+c₂ < A) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → let a := overhead Q D w
      C * 2^(evalDepth w k A c₁ a q) * w^c₂ ≤
        UniversalTick.clock w UniversalTick.saving * ticks k a q := by
  let c₀ := UniversalTick.saving
  filter_upwards [UniversalTick.fits_round c₀,TraceDistribution.polynomial_room 1 A,
    eventually_ge_atTop (max 2 (8*C*2^c₁))] with w room den large
  intro q qpos _
  let a := overhead Q D w
  let T := (side a)^k
  let m := UniversalTick.clock w c₀
  let V := 2^w
  let B := pairs A w q
  have wp : 1≤w := by omega
  have db : w^A≤V := (Nat.pow_le_pow_left (Nat.le_succ w) A).trans
    (le_trans (by simpa using den) (Nat.pow_le_pow_right (by decide) (Nat.div_le_self w 100)))
  have denpos : 0<w^A := Nat.pow_pos wp
  have top : w^A≤q*V := db.trans (Nat.le_mul_of_pos_left _ qpos)
  have Bpos : 0<B := by
    apply Nat.pos_of_ne_zero
    intro eqn
    have h := (ceilDiv_le_iff_le_mul denpos).mp (show q*V ⌈/⌉ w^A ≤ 0 by exact eqn.le)
    simp only [Nat.mul_zero] at h
    omega
  have cash : B*w^A ≤ 2*(q*V) := calc
    _ ≤ q*V+w^A-1 := by
      change ((q*V+w^A-1)/w^A)*w^A ≤ _
      exact Nat.div_mul_le_self _ _
    _ ≤ _ := by omega
  have mcash := (UniversalTick.rounded w c₀ wp room).2
  change V≤2*(m*w^c₀) at mcash
  have exp : 8*C*2^c₁ * w^(c₀+c₁+c₂) ≤ w^A := calc
    _ ≤ w*w^(c₀+c₁+c₂) := Nat.mul_le_mul_right _ (by omega)
    _ = w^(c₀+c₁+c₂+1) := by ring
    _ ≤ _ := Nat.pow_le_pow_right wp saving
  have clocked := (cap_round w k A c₁ a q
    (show 0<T*B*(w+1)^c₁ from Nat.mul_pos
      (Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _)) Bpos) (Nat.pow_pos (Nat.succ_pos _)))).2
  change 2^evalDepth w k A c₁ a q ≤ 2*(T*B*(w+1)^c₁) at clocked
  have poly : (w+1)^c₁ ≤ 2^c₁*w^c₁ := by
    rw [←mul_pow]
    apply Nat.pow_le_pow_left (by omega)
  have scale : 0 < 2*w^c₀*w^A := Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos wp)) denpos
  change _ ≤ m*(T*q)
  apply Nat.le_of_mul_le_mul_left (c:=2*w^c₀*w^A) _ scale
  calc
    _ ≤ (2*w^c₀*w^A)*(C*(2*(T*B*(2^c₁*w^c₁)))*w^c₂) := by
      have high := clocked.trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (T*B) poly))
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C high))
    _ = 4*C*2^c₁*w^(c₀+c₁+c₂)*T*(B*w^A) := by simp only [pow_add]; ring
    _ ≤ 4*C*2^c₁*w^(c₀+c₁+c₂)*T*(2*(q*V)) := Nat.mul_le_mul_left _ cash
    _ = (8*C*2^c₁*w^(c₀+c₁+c₂))*(T*q)*V := by ring
    _ ≤ w^A*(T*q)*(2*(m*w^c₀)) := Nat.mul_le_mul (Nat.mul_le_mul_right _ exp) mcash
    _ = _ := by ring

end Hierarchy.GridScale

end OAI
