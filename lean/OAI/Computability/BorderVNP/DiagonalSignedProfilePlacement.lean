import OAI.Computability.BorderVNP.DiagonalPhysicalGeometryStripe
import OAI.Computability.BorderVNP.DiagonalCubeStartupWorkspace
import OAI.Computability.BorderVNP.DiagonalExternalFreeGroups
import OAI.Computability.BorderVNP.TransmissionJointReads
import OAI.Computability.BorderVNP.FiniteProcessorScale

/-! # The signed profile's two physical stripes and its reserved geometry addresses

The signed reference is already carried in the single distributed reference bit.
The optional first stripe therefore has zero width. The second stripe stores the
whole reserved geometry table. Its inputs, outputs and resulting native memory
use the same allocation, after the seven-word demand rows on the true bottom grid.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Crossing Cover Packing ExternalSew PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule RoutingISA GeometryAdvice GeometryAdviceRate
open TeamContraction TeamContraction.ProcessorSlots VPVNP
open scoped Classical BorderVNP.Epoch.Cube

/-- The signed reference reader uses the dedicated one-bit field per processor. -/
def signedBootStripe (start : ℕ) : Stripe := ⟨start,0,0,0⟩

universe u
variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {extra E dlog Q A B j : ℕ} (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra}

set_option maxHeartbeats 1200000 in
/-- At a single threshold, every paid reserved table occupies the correct second
stripe and has an addressable end sentinel. The directory has exactly one row
per expanded leaf and initial tile, two true input fields and the selected
cover block width. All supplied gate numbers may already include padding. -/
theorem JointSchedule.eventually_signed_profile_placement (b : JointSchedule.{u} s (E+1) dlog Q A B j)
    (power : E+2 ≤ dlog) (physical : UniversalMachine.Program) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n
      let w := b.physical.word n
      let link := b.physical.link n
      let lit := literal s.α n
      let start := freeStartWith physical r 32 64 w n
      let free := FieldProcessor.freeWidth physical s.α 32 64 r w n
      let V := CoverScale.sites (Epoch.Cube D) (CoverScale.initialDepth (Epoch.Cube D) r n)
      let entries := (epochCopies S)^epochs s.τ n*V
      ∀ (desc len copied reserve gates outputs bits : ℕ), (len:ℝ) ≤ r*(n:ℝ)^(24/25:ℝ) → copied ≤ r →
        1 ≤ bits → packetWords gates reserve outputs bits*w ≤ r*width n (95/100:ℝ) →
        let dir := freeDirectory R r lit link V (blockWidth (r*n) V) entries desc
        let arena : StartupArena := ⟨R+1,r,lit,link,len,copied⟩
        let fresh := arena.next+7*dir.candidates
        let ell := stripeWidth (packetWords gates reserve outputs bits*w) r
        JointRoom dir start free (signedBootStripe start) (Allocation.stripe fresh reserve gates outputs bits (lit/4) ell) ∧
        Allocation.stop fresh reserve gates outputs bits w < 2^w := by
  filter_upwards [b.eventually_geometry_literal_stripe power physical 32 64,
    b.eventually_cube_startup_workspace cube,b.eventually_word_capacity 2 1,eventually_ge_atTop 1]
      with n stripes space cap hn
  intro r R w link lit start free V entries desc len copied reserve gates outputs bits head hc hb cost dir arena fresh ell
  have h := stripes _ cost
  have hs : start < lit/4 := h.1
  have hu : start ≤ lit := hs.le.trans (Nat.div_le_self ..)
  have hr : 1 ≤ r := stretch_one ..
  have ha : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have exp : 1-(s.α:ℝ)/3 ≤ 1 := by linarith
  have litBound : lit ≤ n := Nat.floor_le_of_le (by
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1 ≤ (n:ℝ)) exp)
  have cell := space dir len copied (r*n) reserve gates outputs bits head hc (Nat.mul_pos hr hn)
    (Nat.mul_le_mul_left _ litBound) le_rfl rfl rfl rfl (by exact Nat.le_refl 2) rfl rfl hb cost
  have bound : 2*(r*n+1)^1 < 2^w := cap.2.2.1
  refine ⟨⟨?_,le_rfl,hs.le,?_⟩,?_⟩
  · change start+(lit-start) = lit
    omega
  · exact h.2.2.2
  · have address : 2*r*n < 2^w := by
      rw [Nat.mul_assoc]
      simpa only [pow_one] using (Nat.mul_le_mul_left 2 (Nat.le_succ (r*n))).trans_lt (by simpa only [pow_one] using bound)
    exact cell.2.1.trans_lt address

end Diagonal

end BorderVNP
end Computability
end OAI
