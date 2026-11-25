import OAI.Hierarchy.ProbeIntegerBatch

namespace OAI
/-! # A single native histogram mass for a finite menu of packet widths -/

namespace Hierarchy.ProtocolRAM
open scoped BigOperators Classical
noncomputable section

/-- A finite price menu uses one common count field at all its physical rows.
Different packets still consume their own actual bit width per copy. -/
def commonWidth {J : Type*} [Fintype J] (width : J→ℕ) := 1+∑ j,width j

theorem width_le_common {J : Type*} [Fintype J] (width : J→ℕ) (j : J) : width j≤commonWidth width :=
  (Finset.single_le_sum (fun x _=>Nat.zero_le (width x)) (Finset.mem_univ j)).trans
    (by unfold commonWidth; omega)

theorem common_copies {J : Type*} [Fintype J] (width : J→ℕ) (j : J) (K payload : ℕ)
    (unit : 0<width j) (scale : 0<K) (large : 2*(K*commonWidth width)≤payload) :
    let B := commonWidth width
    let copies := payload/(K*B)
    (payload:ℝ)/(2*K*B) ≤ (width j:ℝ)*copies ∧ (width j:ℝ)*copies ≤ (payload:ℝ)/K := by
  let B := commonWidth width
  let copies := payload/(K*B)
  have hb : 0<B := by dsimp [B,commonWidth]; omega
  have kR : (0:ℝ)<K := by exact_mod_cast scale
  have bR : (0:ℝ)<B := by exact_mod_cast hb
  have leftRight := AdaptiveProbe.copied_bits (b:=B) scale hb large
  change (payload:ℝ)/(2*K)≤B*(copies:ℝ) ∧ (B:ℝ)*copies≤(payload:ℝ)/K at leftRight
  have small : (1:ℝ)≤width j := by exact_mod_cast unit
  have big : (width j:ℝ)≤B := by exact_mod_cast width_le_common width j
  have nonneg : (0:ℝ)≤copies := by positivity
  refine ⟨?_,(mul_le_mul_of_nonneg_right big nonneg).trans leftRight.2⟩
  have al : (payload:ℝ)/(2*K*B)≤copies := by
    rw [div_mul_eq_div_div,div_le_iff₀ bR,mul_comm]
    simpa only [mul_comm] using leftRight.1
  exact al.trans (by simpa using mul_le_mul_of_nonneg_right small nonneg)

/-- Lower certification uses K times the finite common width. Upper inventory and
quadratic estimates use the original K. Both inequalities refer to the same exact
integer histogram installed by the controller. -/
theorem common_copies_sandwich {J : Type*} [Fintype J] (width : J→ℕ) (j : J) (K payload : ℕ)
    (unit : 0<width j) (scale : 0<K) :
    let B := commonWidth width
    AdaptiveProbe.copied (K*B) (width j) payload ≤ payload/(K*B) ∧
      payload/(K*B) ≤ AdaptiveProbe.copied K (width j) payload := by
  let B := commonWidth width
  have hb : 0<B := by dsimp [B,commonWidth]; omega
  exact ⟨Nat.div_le_div_left (Nat.le_mul_of_pos_right _ unit) (Nat.mul_pos scale hb),
    Nat.div_le_div_left (Nat.mul_le_mul_left K (width_le_common width j)) (Nat.mul_pos scale unit)⟩

theorem quotes_narrow {J : Type*} [Fintype J] (width : J→ℕ) (j : J) (K payload : ℕ)
    (unit : 0<width j) (scale : 0<K) {γ used installed broadcast : ℝ} (gain : 0≤γ)
    (record : installed+broadcast+((payload/(K*commonWidth width):ℕ):ℝ)*(width j*γ/2)≤used) :
    installed+broadcast+(AdaptiveProbe.copied (K*commonWidth width) (width j) payload : ℝ)*
      (width j*γ/2)≤used := by
  have mass : (AdaptiveProbe.copied (K*commonWidth width) (width j) payload:ℝ)≤
      ((payload/(K*commonWidth width):ℕ):ℝ) := by
    exact_mod_cast (common_copies_sandwich width j K payload unit scale).1
  have bound := mul_le_mul_of_nonneg_right mass (show 0≤(width j:ℝ)*γ/2 by positivity)
  linarith only [bound,record]

theorem width_fits_ledger {J : Type*} [Fintype J] (width : J→ℕ) (j : J) (K payload : ℕ)
    (room : 2*(K*commonWidth width)*commonWidth width≤payload) :
    2*((K*commonWidth width)*width j)≤payload := by
  rw [←Nat.mul_assoc]
  exact (Nat.mul_le_mul_left _ (width_le_common width j)).trans room

theorem curvature_narrow {R ρ γ : ℝ} {K B : ℕ} (positive : 0<K) (nonempty : 0<B)
    (large : 8*R*B≤ρ*γ*K) : R/(K:ℝ)^2≤ρ*γ/(8*(K*B:ℕ)) := by
  have k : (0:ℝ)<K := by exact_mod_cast positive
  have b : (0:ℝ)<B := by exact_mod_cast nonempty
  rw [Nat.cast_mul,div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_right large k.le]

end
end Hierarchy.ProtocolRAM

end OAI
