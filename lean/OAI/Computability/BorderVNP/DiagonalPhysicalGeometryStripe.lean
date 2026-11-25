import OAI.Computability.BorderVNP.DiagonalPhysicalGeometryClock

/-! # Geometry-stripe placement at the selected RAM word on the true processor literal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Packing PackedHistoryCircuit.Normalized
open GeometryAdviceRate TeamContraction TeamContraction.ProcessorSlots VPVNP

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m} {S : SiteSchedule e}
    {a extra E dlog Q A B j : ℕ} {s : EpochScales S a extra}

/-- The complete physical program prefix, the geometry bit stripe and the
original private half-literal occupy disjoint parts of the same processor
word. The charged packet is serialized at the true joint-schedule width.
The result holds for each fixed signed or field-valued hardware program. -/
theorem JointSchedule.eventually_geometry_literal_stripe (b : JointSchedule.{u} s (E+1) dlog Q A B j)
    (power : E+2 ≤ dlog) (p : UniversalMachine.Program) (args regs : ℕ) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let w := b.physical.word n
      ∀ bits : ℕ, bits ≤ r*width n (95/100:ℝ) →
        entryLiteral p (w+1) n (prefixCapacity r args regs w n+1) < literal s.α n/4 ∧
        bits ≤ r*stripeWidth bits r ∧ stripeWidth bits r ≤ literal s.α n/8 ∧
        literal s.α n/4+stripeWidth bits r ≤ literal s.α n-literal s.α n/2 := by
  let C := (UniversalMachine.programPrefix p).length+(args+regs+12)+12+16
  have exponent : 0 < 1-(s.α:ℝ)/3 := by linarith only [s.alpha_small]
  filter_upwards [b.eventually_lengths 0,eventually_ge_atTop 1,
    eventually_le_rounded_width (by linarith only [s.tau_small,s.alpha_small] : (s.τ:ℝ)/2000 < 1-(s.α:ℝ)/3) exponent
      (by norm_num : (0:ℝ) < 1/8) C,
    eventually_le_rounded_width (by linarith only [s.alpha_small] : (95/100:ℝ) < 1-(s.α:ℝ)/3) exponent
      (by norm_num : (0:ℝ)<1) 16,
    eventually_le_rounded_width exponent exponent (by norm_num : (0:ℝ)<1) 8] with n lengths hn head stripe floor
  intro r w bits paid
  let L := logWidth r n
  let pre := entryLiteral p (w+1) n (prefixCapacity r args regs w n+1)
  have hr := stretch_one b.ρ n
  have hL : 1 ≤ L := (indexWidths hr hn).1
  have smallW : (w:ℝ) ≤ (n:ℝ)^((s.τ:ℝ)/2000) := by
    change ((L^(E+2):ℕ):ℝ) ≤ _
    rw [Nat.cast_pow]
    exact (pow_le_pow_right₀ (by exact_mod_cast hL : (1:ℝ) ≤ L) power).trans lengths.logs
  have Lw : L ≤ w := Nat.le_self_pow (by omega : E+2 ≠ 0) L
  have wpos := hL.trans Lw
  have preW : pre ≤ C*w := calc
    _ ≤ (UniversalMachine.programPrefix p).length + (args+regs+12)*w + 12*L+16 := prefix_le p args regs w hr hn
    _ ≤ (UniversalMachine.programPrefix p).length*w + (args+regs+12)*w + 12*w+16*w :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right (Nat.le_mul_of_pos_right _ wpos) _) (Nat.mul_le_mul_left 12 Lw))
        (Nat.le_mul_of_pos_right _ wpos)
    _ = _ := by simp only [C,Nat.add_mul]
  have preScale : (pre:ℝ) ≤ (C:ℝ)*(n:ℝ)^((s.τ:ℝ)/2000) :=
    (show (pre:ℝ) ≤ (C:ℝ)*w by exact_mod_cast preW).trans
      (mul_le_mul_of_nonneg_left smallW (Nat.cast_nonneg _))
  have litRoom : 8*pre ≤ literal s.α n := by
    change (C:ℝ)*(n:ℝ)^((s.τ:ℝ)/2000) ≤ (1/8:ℝ)*literal s.α n at head
    exact_mod_cast (show (8:ℝ)*pre ≤ literal s.α n by linarith only [preScale,head])
  have low : 8 ≤ literal s.α n := by simpa only [Real.rpow_zero,mul_one,one_mul,literal,←Nat.cast_ofNat (R := ℝ),Nat.cast_le] using floor
  have nOne : (1:ℝ) ≤ n := by exact_mod_cast hn
  have count : 1 ≤ width n (95/100:ℝ) := Nat.le_floor (by simpa using Real.one_le_rpow nOne (by norm_num : (0:ℝ) ≤ 95/100))
  have str : stripeWidth bits r ≤ width n (95/100:ℝ) := max_le count ((ceilDiv_le_iff_le_mul hr).mpr paid)
  have bound : 16*width n (95/100:ℝ) ≤ literal s.α n := by
    have rounded : (width n (95/100:ℝ):ℝ) ≤ (n:ℝ)^(95/100:ℝ) := Nat.floor_le (by positivity)
    have rhs : (16:ℝ)*(n:ℝ)^(95/100:ℝ) ≤ (literal (s.α:ℝ) n:ℝ) := by
      simpa only [literal,one_mul] using stripe
    have cap : (16:ℝ)*width n (95/100:ℝ) ≤ literal s.α n :=
      (mul_le_mul_of_nonneg_left rounded (by norm_num : (0:ℝ) ≤ 16)).trans rhs
    exact_mod_cast cap
  exact ⟨by change pre < _; omega,stripe_capacity bits hr,by omega,by omega⟩

end Diagonal

end BorderVNP
end Computability
end OAI
