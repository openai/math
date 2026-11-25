import OAI.Computability.BorderVNP.PackedTerminalRoutingCapacity
import OAI.Computability.BorderVNP.PackedHistoryGeometryRate

/-! # Native clock for the emitted terminal rows of the actual grid history

The selected circuit uses a linear number of row operations up to fixed
powers of the machine word. The full original grid rectangle, exterior
four-slot cable table, original and live placements, and all output bits
are charged before applying the native advice clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch Packing Shortening Diagonal TeamScales Filter
open VPVNP.VerifierNetwork GeometryAdviceRate
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {a x : ℕ} (scale : EpochScales S a x)

/-- The physical geometry interpreter and its serialized advice take strictly
less than the paper's 0.93 bound. The true terminal rectangle controls the
row-dependent part, including scalar outputs and their actual bit widths.
The separately charged shared work permits a cumulative staging-width pass
through the interior history. -/
theorem eventually_terminal_program (D₁ D₂ : ℕ) :
    ∃ ω : ℝ, 0<ω ∧ ∀ H A B : ℝ, 0≤H → 0≤A → 0≤B →
      ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
      let start := CoverScale.initialDepth (Cube D) r n
      let tiles := CoverScale.sites (Cube D) start
      let T := epochs scale.τ n
      let fan := S.fanIn^S.rounds
      let live := teams scale.α scale.τ fan n*tiles
      ∀ C ≤ tiles, let R := routingRows (boundary S start T) C (fan^T*tiles) live
      ∀ {X Y V : Type} [Fintype X] [Fintype Y] [Fintype V] {active reserve o b : ℕ}
        (W shared : ℕ) (history : Frame (X ⊕ Y) (V ⊕ Unit)) (order : Y ≃ Fin active) (fit : active ≤ reserve)
        (emit : Frame ((X ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (input : X → Bool),
        1≤b → (W:ℝ) ≤ B*(logWidth r n:ℝ)^D₂ →
        ((history.size+3*(reserve-active)+3+reserve+shared:ℕ):ℝ) ≤ H*r*(n:ℝ)^(92/100:ℝ) →
        ((emit.size+o*b:ℕ):ℝ) ≤ shared+A*R*(logWidth r n:ℝ)^D₁ →
        let table := geometryTable history order fit emit input
        ((GeometryAdviceRate.ticks table.size reserve o b W+packetWords table.size reserve o b*W:ℕ):ℝ) <
          r*(n:ℝ)^(93/100:ℝ) := by
  have hα : (93/100:ℝ)<1-(scale.α:ℝ)/3 := by linarith [scale.alpha_small]
  obtain ⟨ω,positive,clock⟩ := eventually_paper_clock D₁ D₂ hα
  refine ⟨ω,positive,fun H A B hH hA hB => ?_⟩
  filter_upwards [eventually_routing_rows S scale,clock (H+A) B (add_nonneg hH hA) hB,eventually_ge_atTop 1]
    with n rowN time hn
  intro r hr hrω start tiles T fan live C cfits R X Y V _ _ _ active reserve o b W shared history order fit emit input hb hw his rows table
  have lo := rowN r hr C cfits
  change (R:ℝ) ≤ r*(n:ℝ)^(91/100:ℝ) at lo
  have hi := lo.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ)≤n) (by norm_num : (91/100:ℝ)≤92/100)) (Nat.cast_nonneg r))
  have hL : (1:ℝ) ≤ logWidth r n := by exact_mod_cast (GeometryAdviceRate.indexWidths hr hn).1
  have one : (1:ℝ) ≤ (logWidth r n:ℝ)^D₁ := one_le_pow₀ hL
  have size : ((history.size+emit.size+3*(reserve-active)+3+reserve+o*b:ℕ):ℝ) ≤
      (H+A)*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^D₁ := by
    rw [show history.size+emit.size+3*(reserve-active)+3+reserve+o*b =
      (history.size+3*(reserve-active)+3+reserve)+(emit.size+o*b) by omega,Nat.cast_add]
    have hsum : ((history.size+3*(reserve-active)+3+reserve:ℕ):ℝ)+((emit.size+o*b:ℕ):ℝ) ≤
        H*r*(n:ℝ)^(92/100:ℝ)+A*R*(logWidth r n:ℝ)^D₁ := by
      push_cast only [Nat.cast_add] at his rows ⊢
      linarith only [his,rows]
    calc
      _ ≤ H*r*(n:ℝ)^(92/100:ℝ)+A*R*(logWidth r n:ℝ)^D₁ := hsum
      _ ≤ H*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^D₁ +
        A*((r:ℝ)*(n:ℝ)^(92/100:ℝ))*(logWidth r n:ℝ)^D₁ := add_le_add
          (le_mul_of_one_le_right (by positivity) one)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hA) (by positivity))
      _ = _ := by ring
  exact time r (history.size+emit.size+3*(reserve-active)+3) table.size reserve o b W hr hrω hb
    (exportRows_size history order fit emit input) size hw

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
