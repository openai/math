import OAI.Computability.BorderVNP.GeometryGateCeiling

/-! # The reserved sparse geometry at the chosen joint batch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Cover Packing PackedHistoryCircuit PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule VPVNP.VerifierNetwork GeometryAdviceRate
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m} {S : SiteSchedule e}
variable {a extra E dlog Q A B j : ℕ} {s : EpochScales S a extra}


/-- Combine the charged augmented history, the reserved profile and the terminal
routing-row polynomial on the same actual branch. A public projection charged
to the history can occur in the emitter through the fixed multiplier Q. -/
theorem JointSchedule.eventually_reserved_geometry_charge
    (b : JointSchedule.{u} s (E+1) dlog Q A B j) (degree U : ℕ) (power : degree+(E+2) ≤ dlog) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let w := b.physical.word n
      let R := b.physical.teamsPred n+1
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let t := epochs s.τ n
      let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start t)
      let J := (epochCopies S)^t*V
      let rows := routingRows (boundary S start t) cells J (R*V)
      let reserve := SeedPlan.profileReserve r n
      ∀ {X Y P : Type*} [Fintype X] [Fintype Y] [Fintype P] {active o field mult : ℕ}
        (history : Frame (X ⊕ Y) (P ⊕ Unit)) (order : Y ≃ Fin active) (fit : active ≤ reserve)
        (emit : Frame ((X ⊕ Fin reserve) ⊕ P) (Fin o × Fin field)) (x : X → Bool),
        1 ≤ field → ((mult*history.size+active:ℕ):ℝ) ≤ r*(n:ℝ)^(92/100:ℝ) →
        history.size+emit.size+o*field ≤ mult*history.size+U*rows*(logWidth r n)^degree →
        let table := geometryTable history order fit emit x
        let ceiling := geometryGateCeiling U degree r n
        let bits := packetWords ceiling reserve o field*w
        table.size ≤ ceiling ∧ (table.reserve ceiling).size=ceiling ∧
        (GeometryAdviceRate.ticks ceiling reserve o field w+bits+reserve+deliveryScanTicks J R V:ℕ) <
          (r:ℝ)*(n:ℝ)^(93/100:ℝ) ∧
          GeometryAdviceRate.ticks ceiling reserve o field w+bits ≤ r*TeamScales.width n (95/100:ℝ) := by
  filter_upwards [b.eventually_numeric_geometry_charge degree power (2*(U+8)) (by positivity),
    eventually_compiled_dimensions S s,eventually_ge_atTop 1] with n clock dimensions hn
  intro r w R start V t cells J rows reserve X Y P _ _ _ active o field mult hist ord fit emit x fieldPos paid cost table ceiling bits
  have one : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hr := stretch_one b.ρ n
  have rr := (dimensions r hr).2.1
  have count := (b.sizes hn).1
  change R = TeamScales.teams s.α s.τ (S.fanIn^S.rounds) n at count
  rw [← count] at rr
  have rowFit : (rows:ℝ) ≤ r*(n:ℝ)^(92/100:ℝ) := rr.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le one (by norm_num)) (Nat.cast_nonneg r))
  obtain ⟨rawSize,reservedSize,size⟩ := geometry_reserve_components hn hr hist ord fit emit x paid rowFit cost
  exact ⟨rawSize,reservedSize,clock fieldPos (Nat.le_refl ceiling) size⟩

end Diagonal

end BorderVNP
end Computability
end OAI
