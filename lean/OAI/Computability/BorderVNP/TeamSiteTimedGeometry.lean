import OAI.Computability.BorderVNP.FiniteProcessorScale
import OAI.Computability.BorderVNP.TeamSiteTimedCoefficient
import OAI.Computability.BorderVNP.DiagonalSewnTape

/-! # Physical geometry for the trusted private timer and the sewn parse table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP UniversalMachine TeamScales TeamContraction TeamContraction.ProcessorSlots TeamSite Filter
open private start_le from OAI.Computability.BorderVNP.FiniteProcessorScale
open private log_dominates from OAI.Computability.BorderVNP.TeamProcessorLiteralScale

/-- One team exponent suffices for every fixed processor table, including the
table with a trusted timer. All startup words, both literal copies and the actual
interior sorting edges fit, uniformly in the number of exterior teams. -/
theorem eventually_programGeometry (D : ℕ) {α ξ : ℝ} (hα : α < 3) (hξ : 0 < ξ)
    (hsmall : ξ < 3/2) (horder : ξ ≤ α) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ {pc reg args routines m g : ℕ} {Q Γ : Type} [Fintype Q]
      (_P : TeamOpcode.Program pc reg args routines) (_lib : Fin routines → Macro Q Γ m g)
      (physical : Program), ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 0 < r →
        (r : ℝ) ≤ (2 : ℝ)^((n : ℝ)^ω) → ∀ other : ℕ,
        Scale physical pc reg args α ξ r n other (logWidth r n^(D+1)) (Wires.sortExponent (block ξ n)) := by
  obtain ⟨u,hu,sites⟩ := eventually_siteGeometry D hα hξ hsmall horder
  obtain ⟨v,hv,caps⟩ := exists_common_exponent (D+1) hα hξ
  refine ⟨min u v,lt_min hu hv,?_⟩
  intro pc reg args routines m g Q Γ inst P lib physical
  let C := 2*((programPrefix physical).length+args+reg+48)
  filter_upwards [sites P lib,caps C,eventually_ge_atTop 1] with n site cap hn
  intro r hr bound other
  have geo := site r hr (admissible_smaller hn (min_le_left ..) bound) other
  have room := (cap r hr (admissible_smaller hn (min_le_right ..) bound)).1
  have wide : logWidth r n ≤ logWidth r n^(D+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (log_dominates hr hn).1 (show 1 ≤ D+1 by omega)
  apply Scale.of_reserved P lib physical geo
  exact (Nat.mul_le_mul_left 2 (start_le physical args reg r _ n hr hn wide)).trans (by rwa [← Nat.mul_assoc])

end FieldProcessor

namespace TeamSite.TimedProcessor

open VPVNP TeamContraction TeamContraction.ProcessorSlots

/-- The installed native processor and the sewn polynomial row have the same
physical wiring. Each free string includes the true globally addressed parser
header and the site data chosen after the template. -/
theorem wiringWith_eq_sewn {pc reg args routines R r w a k e : ℕ}
    (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc reg args routines)
    (S : SiteData R r reg args w a) (pins link : ℕ)
    (fit : fitsWith physical reg args r w a R link (k+1) e) :
    wiringWith physical P S pins link (k+1) e fit =
      Diagonal.CellEntries.SewnTape.wiring physical fit
        (fun u j => entryTail (w+1) (k+1)
          (j.val*entryStride physical (w+1) (k+1) (prefixCapacity r args reg w (k+1)+1+a) R link)
          (2^e) (S.siteBits P (k+1) e u j)) pins := rfl

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
