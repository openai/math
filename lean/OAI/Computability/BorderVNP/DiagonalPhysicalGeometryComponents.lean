import OAI.Computability.BorderVNP.DiagonalPhysicalGeometryStripe

/-! # Paying for the true sparse terminal emitter on the augmented geometry history -/

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


/-- The total Boolean circuit and output width from the charged history and
the additional terminal emitter. The reserved profile is exactly the floor
of the geometry budget, independent of the current branch. -/
theorem geometry_size_of_components {n r hist active emit o field mult rows degree U : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r)
    (paid : ((mult*hist+active:ℕ):ℝ) ≤ r*(n:ℝ)^(92/100:ℝ))
    (rowFit : (rows:ℝ) ≤ r*(n:ℝ)^(92/100:ℝ))
    (cost : hist+emit+o*field ≤ mult*hist+U*rows*(logWidth r n)^degree) :
    let reserve := SeedPlan.profileReserve r n
    ((hist+emit+3*(reserve-active)+3+reserve+o*field:ℕ):ℝ) ≤
      ((U:ℝ)+8)*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^degree := by
  intro reserve
  let Z := (r:ℝ)*(n:ℝ)^(92/100:ℝ)
  let L := logWidth r n
  have one : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have zpos : 1 ≤ Z := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hr) (Real.one_le_rpow one (by norm_num))
  have logs : 1 ≤ (L:ℝ)^degree := one_le_pow₀ (by exact_mod_cast (indexWidths hr hn).1)
  have reserveFit : (reserve:ℝ) ≤ Z := Nat.floor_le (by positivity)
  have padding : ((reserve-active:ℕ):ℝ) ≤ Z := ((Nat.cast_le (α := ℝ)).mpr (Nat.sub_le reserve active)).trans reserveFit
  have gates : ((hist+emit+o*field:ℕ):ℝ) ≤ Z + U*Z*(L:ℝ)^degree := by
    apply ((Nat.cast_le (α := ℝ)).mpr cost).trans
    rw [Nat.cast_add,Nat.cast_mul (U*rows),Nat.cast_mul U,Nat.cast_pow]
    refine add_le_add ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left rowFit (Nat.cast_nonneg U)) (by positivity))
    exact ((Nat.cast_le (α := ℝ)).mpr (Nat.le_add_right (mult*hist) active)).trans paid
  have zlog : Z ≤ Z*(L:ℝ)^degree := le_mul_of_one_le_right (zero_le_one.trans zpos) logs
  rw [mul_assoc ((U:ℝ)+8) (r:ℝ) ((n:ℝ)^(92/100:ℝ))]
  change _ ≤ ((U:ℝ)+8)*Z*(L:ℝ)^degree
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at gates ⊢
  nlinarith only [gates,padding,reserveFit,zpos,zlog]

/-- Combine the charged augmented history, the reserved profile and the terminal
routing-row polynomial on the same actual branch. A public projection charged
to the history can occur in the emitter through the fixed multiplier Q. -/
theorem JointSchedule.eventually_geometry_component_charge
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
        let g := (geometryTable history order fit emit x).size
        let bits := packetWords g reserve o field*w
        (GeometryAdviceRate.ticks g reserve o field w+bits+reserve+deliveryScanTicks J R V:ℕ) <
          (r:ℝ)*(n:ℝ)^(93/100:ℝ) ∧
          GeometryAdviceRate.ticks g reserve o field w+bits ≤ r*TeamScales.width n (95/100:ℝ) := by
  filter_upwards [b.eventually_geometry_reconstruction_charge degree power (U+8) (by positivity),
    eventually_compiled_dimensions S s,eventually_ge_atTop 1] with n clock dimensions hn
  intro r w R start V t cells J rows reserve X Y P _ _ _ active o field mult hist ord fit emit x fieldPos paid cost g bits
  have one : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hr := stretch_one b.ρ n
  have rr := (dimensions r hr).2.1
  have count := (b.sizes hn).1
  change R = TeamScales.teams s.α s.τ (S.fanIn^S.rounds) n at count
  rw [← count] at rr
  have rowFit : (rows:ℝ) ≤ r*(n:ℝ)^(92/100:ℝ) := rr.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le one (by norm_num)) (Nat.cast_nonneg r))
  exact clock hist ord fit emit x fieldPos (geometry_size_of_components hn hr paid rowFit cost)

end Diagonal

end BorderVNP
end Computability
end OAI
