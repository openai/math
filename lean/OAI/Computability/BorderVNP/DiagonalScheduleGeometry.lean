import OAI.Computability.BorderVNP.DiagonalAdmissibleRange
import OAI.Computability.BorderVNP.TransmissionJointGeometry

/-! # Geometry, packet stream and tail estimates on the same processor range -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales TeamContraction TeamContraction.ProcessorSlots VPVNP.BurstRAM
open GeometryAdviceRate (packetWords)

variable {pc m g : ℕ} {Q Γ : Type} [Fintype Q]

/-- Physical geometry and stream for the 64-register, 32-argument evaluator. -/
def jointGeometryAt (P : TeamOpcode.Program pc 64 32 8) (lib : Fin 8 → TeamSite.Macro Q Γ m g)
    (E d copies : ℕ) (α τ A B : ℝ) (n r : ℕ) : Prop :=
  ∀ V dB original gates u o b dense : ℕ, ∀ L : Packing.Directory.Layout,
    1 ≤ b → gates ≤ 4*original →
    ((original+u+o*b:ℕ):ℝ) ≤ A*r*(n:ℝ)^(93/100:ℝ)*(logWidth r n:ℝ)^d →
    ((V*dB:ℕ):ℝ) ≤ B*volume τ r n*(logWidth r n:ℝ)^d →
    (dB:ℝ) ≤ B*(logWidth r n:ℝ)^d → L.literal = literal α n →
    let W := logWidth r n^(E+1)
    let R := teams α τ copies n
    let start := freeStart P lib r W n
    let words := packetWords gates u o b
    let bits := words*W
    let stripe := geometryStripe L.literal bits r dense words
    SiteGeometry P lib α (τ/5) r n (R-1) W (Wires.sortExponent (block (τ/5) n)) ∧
      JointRoom L start (siteFree P lib α r W n) (emptyBoot start) stripe ∧
      bits ≤ r*stripe.width ∧ GeometryAdviceRate.ticks gates u o b W + bits ≤ r*width n (95/100:ℝ) ∧
      dB ≤ L.literal/2 ∧ copies^epochs τ n*V*dB ≤ R*r*(L.literal/2)

/-- Uniformity in fixed program and library, with both chosen ahead of the input length. -/
def GeometryBudget (E d copies : ℕ) (α τ ω : ℝ) : Prop :=
  ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
    ∀ {pc m g : ℕ} {Q Γ : Type} [Fintype Q]
      (P : TeamOpcode.Program pc 64 32 8) (lib : Fin 8 → TeamSite.Macro Q Γ m g),
      AdmissibleRange ω (jointGeometryAt P lib E d copies α τ A B)

theorem GeometryBudget.shrink {E d copies : ℕ} {α τ u v : ℝ}
    (b : GeometryBudget E d copies α τ v) (huv : u ≤ v) :
    GeometryBudget E d copies α τ u :=
  fun A B ha hb _ _ _ _ _ _ P lib => (b A B ha hb P lib).shrink huv

theorem exists_geometryBudget {α τ : ℝ} (ha : 0 < α) (has : α < 1/1000)
    (ht : 0 < τ) (hts : τ < α/100) (E d copies : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ GeometryBudget E d copies α τ ω := by
  obtain ⟨ω,hω,fit⟩ := eventually_joint_geometry E d ha has ht hts
    (show 0 < τ/5 by positivity) (show τ/5 ≤ α by linarith)
  refine ⟨ω,hω,?_⟩
  intro A B hA hB pc m g Q Γ fq P lib
  filter_upwards [fit A B hA hB P lib] with n hn
  intro r hr room V dB original gates u o b dense L
  exact hn r (teams α τ copies n-1) copies V dB original gates u o b dense L hr room

end Diagonal

end BorderVNP
end Computability
end OAI
