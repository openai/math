import OAI.Computability.BorderVNP.DiagonalCubePublicationRoom
import OAI.Computability.BorderVNP.PackedReconstructionClock

/-! # Native geometry and delivery clocks at the actual selected processor word

The sparse Boolean geometry compiler can use short address fields internally.
Its emitted packet is serialized at the hardware word of the joint schedule.
The logarithmic exponent chosen before the schedule pays for that word
together with the emitter's own polynomial overhead.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Cover Packing PackedHistoryCircuit PackedHistoryCircuit.Normalized
open VPVNP.VerifierNetwork GeometryAdviceRate
open scoped Classical BorderVNP.Epoch.Cube
open private charge_bound from OAI.Computability.BorderVNP.GeometryAdviceRate
open private scan_bound from OAI.Computability.BorderVNP.PackedReconstructionClock

universe u
variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m} {S : SiteSchedule e}
variable {a extra E dlog Q A B j : ℕ} {s : EpochScales S a extra}

set_option maxRecDepth 5000 in
/-- At the chosen stretched batch, admit the genuine interpreter at any numerical
gate count bounded by the Boolean budget, including a length-only reservation. -/
theorem JointSchedule.eventually_numeric_geometry_charge
    (b : JointSchedule.{u} s (E+1) dlog Q A B j) (degree : ℕ) (power : degree+(E+2) ≤ dlog)
    (H : ℝ) (nonneg : 0 ≤ H) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let w := b.physical.word n
      let R := b.physical.teamsPred n+1
      let V := CoverScale.sites (Epoch.Cube D) (CoverScale.initialDepth (Epoch.Cube D) r n)
      let J := (epochCopies S)^(epochs s.τ n)*V
      ∀ {g k reserve o field : ℕ},
        1 ≤ field → k ≤ 4*g →
        ((g+reserve+o*field:ℕ):ℝ) ≤
          H*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^degree →
        let bits := packetWords k reserve o field*w
        let work := GeometryAdviceRate.ticks k reserve o field w+bits+reserve+deliveryScanTicks J R V
        (work:ℝ) < r*(n:ℝ)^(93/100:ℝ) ∧
          GeometryAdviceRate.ticks k reserve o field w+bits ≤ r*TeamScales.width n (95/100:ℝ) := by
  let C : ℝ := 3072*(H+1)*2
  let cost : ℕ := RoutingISA.PrivatePlacement.setup.slots+Directory.ISA.setup.slots+8*Directory.ISA.candidate.slots+200
  let coeff : ℝ := 2*C+2*cost
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have tau : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  filter_upwards [b.eventually_lengths 0,b.eventually_directory_cover,eventually_ge_atTop 1,
    eventually_rpow_gap (by norm_num : (925/1000:ℝ)<93/100) (coeff+1),
    eventually_le_rounded_width (by norm_num : (93/100:ℝ)<95/100) (by norm_num : (0:ℝ)<95/100)
      (by norm_num : (0:ℝ)<1) 1] with n length cover hn gap rounded
  intro r w R V J g k reserve o field fieldPos count size bits work
  let L := logWidth r n
  let N := (n:ℝ)^(925/1000:ℝ)
  have hr := stretch_one b.ρ n
  have one : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have npos := zero_lt_one.trans_le one
  have lpos : 1 ≤ L := (indexWidths hr hn).1
  have lreal : 1 ≤ (L:ℝ) := by exact_mod_cast lpos
  have word : (w:ℝ) ≤ 1*(L:ℝ)^(E+2) := by
    change ((L^(E+2):ℕ):ℝ) ≤ _
    simp
  have measured := charge_bound (σ := 92/100) (E := E+2) (D := degree) (by norm_num)
    hr hn fieldPos count size word
  rw [show (1:ℝ)+1=2 by norm_num] at measured
  change (GeometryAdviceRate.ticks k reserve o field w + bits:ℕ) ≤
    (r:ℝ)*(C*(n:ℝ)^(92/100:ℝ)*(L:ℝ)^(degree+(E+2))) at measured
  have logs : (L:ℝ)^(degree+(E+2)) ≤ (n:ℝ)^((s.τ:ℝ)/2000) :=
    (pow_le_pow_right₀ lreal power).trans length.logs
  have base : (n:ℝ)^(92/100:ℝ)*(L:ℝ)^(degree+(E+2)) ≤ N := calc
    _ ≤ (n:ℝ)^(92/100:ℝ)*(n:ℝ)^((s.τ:ℝ)/2000) := by gcongr
    _ = (n:ℝ)^((92/100:ℝ)+(s.τ:ℝ)/2000) := (Real.rpow_add npos _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one (by linarith only [s.tau_small,s.alpha_small])
  have geometry : (GeometryAdviceRate.ticks k reserve o field w + bits:ℕ) ≤ (r:ℝ)*(C*N) := by
    apply measured.trans
    rw [mul_assoc C]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left base hC) (Nat.cast_nonneg r)
  have jfit : J ≤ R*V := Nat.mul_le_mul_right V cover.2.2
  have rowBound : ((R*V:ℕ):ℝ) ≤ (r:ℝ)*N := calc
    _ ≤ (n:ℝ)^(2*(s.α:ℝ))*(r*(n:ℝ)^(9/10:ℝ)) := by
      rw [Nat.cast_mul]
      exact mul_le_mul length.teams.2 length.cover.2.2.2.1 (Nat.cast_nonneg _) (by positivity)
    _ = (r:ℝ)*(n:ℝ)^(2*(s.α:ℝ)+9/10) := by rw [Real.rpow_add npos]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one (by linarith only [s.alpha_small])) (Nat.cast_nonneg r)
  have rpos : 0 < (r:ℝ) := by exact_mod_cast hr
  have nval : 1 ≤ N := Real.one_le_rpow one (by norm_num)
  have rN : 1 ≤ (r:ℝ)*N := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hr) nval
  have scan : (deliveryScanTicks J R V:ℝ) ≤ 2*cost*((r:ℝ)*N) := calc
    _ ≤ (cost:ℝ)*(((R*V:ℕ):ℝ)+1) := by exact_mod_cast scan_bound J R V jfit
    _ ≤ (cost:ℝ)*(2*((r:ℝ)*N)) := mul_le_mul_of_nonneg_left (by linarith only [rowBound,rN]) (Nat.cast_nonneg cost)
    _ = _ := by ring
  have wpos : 1 ≤ w := Nat.one_le_pow _ _ lpos
  have reserved : reserve ≤ bits := (show reserve ≤ packetWords k reserve o field by unfold packetWords; omega).trans
    (Nat.le_mul_of_pos_right _ wpos)
  have add : (reserve:ℝ) ≤ (r:ℝ)*(C*N) := ((Nat.cast_le (α := ℝ)).mpr
    (reserved.trans (Nat.le_add_left bits (GeometryAdviceRate.ticks k reserve o field w)))).trans geometry
  have all : (work:ℝ) ≤ (r:ℝ)*(coeff*N) := by
    change ((GeometryAdviceRate.ticks k reserve o field w+bits+reserve+deliveryScanTicks J R V:ℕ):ℝ) ≤ _
    rw [Nat.cast_add,Nat.cast_add]
    dsimp only [coeff]
    nlinarith only [geometry,add,scan]
  have strict : coeff*N < (n:ℝ)^(93/100:ℝ) := by
    change (coeff+1)*N ≤ _ at gap
    nlinarith only [gap,zero_lt_one.trans_le nval]
  have final := all.trans_lt (mul_lt_mul_of_pos_left strict rpos)
  refine ⟨final,?_⟩
  apply (Nat.cast_le (α := ℝ)).mp
  rw [Nat.cast_mul]
  exact ((Nat.cast_le (α := ℝ)).mpr (show GeometryAdviceRate.ticks k reserve o field w+bits ≤ work by
    dsimp only [work]; omega)).trans (final.le.trans (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using rounded) (Nat.cast_nonneg r)))

set_option maxRecDepth 5000 in
/-- The whole physical packet, its native evaluation, the reserved profile and
both genuine delivery scans fit the 0.93 bound on the already selected batch.
The threshold precedes the query and wire types as well as the sparse frames.
-/
theorem JointSchedule.eventually_geometry_reconstruction_charge
    (b : JointSchedule.{u} s (E+1) dlog Q A B j) (degree : ℕ) (power : degree+(E+2) ≤ dlog)
    (H : ℝ) (nonneg : 0 ≤ H) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let w := b.physical.word n
      let R := b.physical.teamsPred n+1
      let V := CoverScale.sites (Epoch.Cube D) (CoverScale.initialDepth (Epoch.Cube D) r n)
      let J := (epochCopies S)^(epochs s.τ n)*V
      ∀ {X Y P : Type*} [Fintype X] [Fintype Y] [Fintype P] {active reserve o field : ℕ}
        (history : Frame (X ⊕ Y) (P ⊕ Unit)) (order : Y ≃ Fin active) (fit : active ≤ reserve)
        (emit : Frame ((X ⊕ Fin reserve) ⊕ P) (Fin o × Fin field)) (x : X → Bool),
        1 ≤ field →
        ((history.size+emit.size+3*(reserve-active)+3+reserve+o*field:ℕ):ℝ) ≤
          H*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^degree →
        let g := (geometryTable history order fit emit x).size
        let bits := packetWords g reserve o field*w
        let work := GeometryAdviceRate.ticks g reserve o field w+bits+reserve+deliveryScanTicks J R V
        (work:ℝ) < r*(n:ℝ)^(93/100:ℝ) ∧
          GeometryAdviceRate.ticks g reserve o field w+bits ≤ r*TeamScales.width n (95/100:ℝ) := by
  filter_upwards [b.eventually_numeric_geometry_charge degree power H nonneg] with n charge
  intro r w R V J X Y P _ _ _ active reserve o field hist order fit emit x fieldPos size
  exact charge fieldPos (exportRows_size hist order fit emit x) size

end Diagonal

end BorderVNP
end Computability
end OAI
