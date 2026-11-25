import OAI.Computability.BorderVNP.TransmissionJointProgram
import OAI.Computability.BorderVNP.GeometryAdviceRate
import OAI.Computability.BorderVNP.PackedTailCapacity
import OAI.Computability.BorderVNP.TeamProcessorLiteralScale

/-! # Fitting the joint signed processor, wide geometry and private half-tail -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM TeamScales Filter Packing
open GeometryAdviceRate (stripeWidth packetWords)

/-- The large batch reads the small scalar packet from the single designated bit in
each processor. It needs no second wide boot stripe. -/
def emptyBoot (offset : ℕ) : GeometryAdvice.Stripe := ⟨offset,0,0,0⟩

/-- The shared geometry occupies at most one eighth of the literal starting at one
quarter. The dense pointer is independent of the bit positions in the input. -/
def geometryStripe (literal bits r dense words : ℕ) : GeometryAdvice.Stripe :=
  ⟨literal/4,stripeWidth bits r,dense,words⟩

/-- The source and destination capacities hold together for the actual physical
program, all its native interior slots, the serialized geometry and every private
site description. A single choice of the growth exponent works for arbitrary fixed
description and runtime constants. -/
theorem eventually_joint_geometry (E D : ℕ) {α τ ξ : ℝ}
    (ha : 0 < α) (hsmall : α < 1/1000) (ht : 0 < τ) (hts : τ < α/100) (hx : 0 < ξ) (hxa : ξ ≤ α) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
      ∀ {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q]
        (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g),
      ∀ᶠ n : ℕ in atTop, ∀ (r other K V dB original gates u o b dense : ℕ)
        (L : Packing.Directory.Layout),
        1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) → 1 ≤ b → gates ≤ 4*original →
        ((original+u+o*b:ℕ):ℝ) ≤ A*r*(n:ℝ)^(93/100:ℝ)*(logWidth r n:ℝ)^D →
        ((V*dB:ℕ):ℝ) ≤ B*volume τ r n*(logWidth r n:ℝ)^D →
        (dB:ℝ) ≤ B*(logWidth r n:ℝ)^D → L.literal = literal α n →
        let W := logWidth r n^(E+1)
        let start := freeStart P lib r W n
        let words := packetWords gates u o b
        let bits := words*W
        let stripe := geometryStripe L.literal bits r dense words
        SiteGeometry P lib α ξ r n other W (Wires.sortExponent (block ξ n)) ∧
          JointRoom L start (siteFree P lib α r W n) (emptyBoot start) stripe ∧
          bits ≤ r*stripe.width ∧ GeometryAdviceRate.ticks gates u o b W + bits ≤ r*width n (95/100:ℝ) ∧
          dB ≤ L.literal/2 ∧ K^epochs τ n*V*dB ≤ teams α τ K n*r*(L.literal/2) := by
  obtain ⟨ωs,hs,site⟩ := eventually_siteGeometry E (by linarith : α < 3) hx (by linarith) hxa
  obtain ⟨ωg,hg,geom⟩ := GeometryAdviceRate.eventually_fits D (E+1) (by linarith : (95/100:ℝ) < 1-α/3)
  obtain ⟨ωt,ht',tails⟩ := eventually_private_directory_fits ha hsmall ht hts D
  obtain ⟨ωd,hd,desc⟩ := exists_polylog_budget D (by norm_num : (0:ℝ) < 1/2)
  let ω := min (min ωs ωg) (min ωt ωd)
  refine ⟨ω, lt_min (lt_min hs hg) (lt_min ht' hd), fun A B hA hB pc reg k routines m g Q Γ _ P lib => ?_⟩
  have grow := eventually_le_rounded_width (by linarith : (1/2:ℝ) < 1-α/3) (by linarith : 0 < 1-α/3)
    (by norm_num : (0:ℝ) < 1/2) B
  filter_upwards [site P lib,geom A 1 hA (by norm_num) (TeamSite.Processor.machine P lib) k reg,
    tails B hB,desc,grow,eventually_ge_atTop 1] with n ns ng nt nd nc hn
  intro r other K V dB original gates u o b dense L hr up hb hgate size data single lit W start words bits stripe
  have bound {z : ℝ} (hz : ω ≤ z) := admissible_smaller hn hz up
  have hw : (W:ℝ) ≤ 1*(logWidth r n:ℝ)^(E+1) := by dsimp [W]; norm_cast; omega
  have s := ns r hr (bound ((min_le_left ..).trans (min_le_left ..))) other
  obtain ⟨time,head,cap,_,ends⟩ := ng r original gates u o b W hr (bound ((min_le_left ..).trans (min_le_right ..)))
    hb hgate size hw
  have priv := nt r K V dB hr (bound ((min_le_right ..).trans (min_le_left ..))) data
  have hdB := single.trans ((mul_le_mul_of_nonneg_left
    (nd r hr (bound ((min_le_right ..).trans (min_le_right ..)))) hB).trans nc)
  have twice : 2*dB ≤ L.literal := by
    rw [lit]
    change 2*dB ≤ width n (1-α/3)
    exact_mod_cast (show 2*(dB:ℝ) ≤ (width n (1-α/3):ℝ) by linarith)
  have hstart : start < L.literal/4 := lit ▸ ((freeStart_eq P lib n).trans_lt head)
  have last : stripe.offset+stripe.width ≤ L.literal-L.literal/2 := by
    dsimp [stripe,geometryStripe,bits,words]; rwa [lit]
  refine ⟨s,⟨?_,le_rfl,?_,last⟩,cap,time,by omega,lit ▸ priv⟩
  · change start+(literal α n-start) = L.literal
    rw [← lit]; omega
  · change start+0 ≤ L.literal/4
    omega

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
