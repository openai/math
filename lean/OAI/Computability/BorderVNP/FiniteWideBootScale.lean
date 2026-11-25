import OAI.Computability.BorderVNP.FiniteWideBootRun
import OAI.Computability.BorderVNP.GeometryAdviceRate

/-! # Uniform cost and literal space for the finite-field boot

All 81 extended-frame fields are stored after the physical startup prefix
and before the geometry stripe. The team-size exponent precedes the fixed
program and constant word-growth bound. The same estimates cover the full
interval from one processor to the stretched-exponential batch bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteBoot

open GeometryAdvice RoutingISA TeamContraction VPVNP Filter

/-- Start of the independent bootstrap advice after the program, ordinary
public arguments, handoff fields, and the older one-bit advice slot. -/
def offset (p : UniversalMachine.Program) (args regs r W n : ℕ) :=
  entryLiteral p (W+1) n (ProcessorSlots.prefixCapacity r args regs W n+1)

/-- The actual proven native boot bound at the 81-word finite-field frame. -/
def bootTicks (W : ℕ) := setup.slots + (81*W)*(copyStripeBit.slots+1)+1 +
  (ExtendedFrame.setup.slots+8*81*(W+1)+8)

private theorem ticks_bound (W : ℕ) (hW : 0 < W) : bootTicks W ≤ 4096*W := by
  have h₁ : setup.slots ≤ 100 := by decide
  have h₂ : ExtendedFrame.setup.slots ≤ 100 := by decide
  have h₃ : copyStripeBit.slots+1 = 10 := by decide
  unfold bootTicks
  rw [h₃]
  omega

/-- For every sufficiently large length, every positive batch up to the
chosen upper bound fits both the real processor prefix and the entire
multi-bit boot stripe in the first quarter of the literal. -/
theorem eventually_fits (E : ℕ) {α : ℝ} (hα : (95/100:ℝ) < 1-α/3) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ B : ℝ, 0 ≤ B → ∀ (p : UniversalMachine.Program) (args regs : ℕ),
      ∀ᶠ n : ℕ in atTop, ∀ r W : ℕ, 1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) → 1 ≤ W →
      (W:ℝ) ≤ B*(TeamScales.logWidth r n:ℝ)^E →
      bootTicks W ≤ r*TeamScales.width n (95/100:ℝ) ∧
      offset p args regs r W n + width (81*W) r < TeamScales.literal α n/4 := by
  obtain ⟨ω,hω,all⟩ := GeometryAdviceRate.eventually_fits 0 E hα
  refine ⟨ω,hω,fun B hB p args regs => ?_⟩
  filter_upwards [all 4096 B (by norm_num) hB p (args+81) regs,eventually_ge_atTop 1] with n hn npos
  intro r W hr hbatch hW hword
  have hnreal : (1:ℝ) ≤ n := by exact_mod_cast npos
  have hrreal : (1:ℝ) ≤ r := by exact_mod_cast hr
  have cost : ((0+4096+0*1:ℕ):ℝ) ≤ 4096*r*(n:ℝ)^(93/100:ℝ)*(TeamScales.logWidth r n:ℝ)^0 := by
    simp only [pow_zero,mul_one]
    norm_num
    have one := Real.one_le_rpow hnreal (by norm_num : (0:ℝ) ≤ 93/100)
    nlinarith [mul_le_mul hrreal one (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ r)]
  have h := hn r 0 0 4096 0 1 W hr hbatch le_rfl (by simp) cost hword
  have charge := h.1
  have room := h.2.1
  have packet : GeometryAdviceRate.packetWords 0 4096 0 1 ≥ 4096 := by decide
  have tw := ticks_bound W hW
  have bits := Nat.mul_le_mul_right W packet
  have stripe : width (81*W) r ≤ 81*W := width_le (by omega) hr (Nat.le_mul_of_pos_left _ hr)
  have hoff : offset p args regs r W n + 81*W =
      entryLiteral p (W+1) n (ProcessorSlots.prefixCapacity r (args+81) regs W n+1) := by
    unfold offset entryLiteral ProcessorSlots.prefixCapacity
    ring
  exact ⟨tw.trans (bits.trans ((Nat.le_add_left ..).trans charge)),(Nat.add_le_add_left stripe _).trans_lt (hoff ▸ room)⟩

end FiniteBoot

end BorderVNP
end Computability
end OAI
