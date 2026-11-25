import OAI.Computability.BorderVNP.TeamContractionPhysical

/-! # Integer readout after the checked row dictionary -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP TeamSite TeamSiteConsistency TeamSiteEvents UniversalMachine TeamContraction.Wires Filter
open scoped Classical

variable {p regs k a m g : ℕ} {Q Γ : Type} [Fintype Q]

/-- The fixed compiled program has the true native signed value whenever the concrete
row replay dictionary holds. Its one compilation threshold is independent of the
wire layout, geometry, team size and machine inputs. -/
theorem eventually_value_of_rows (P : TeamOpcode.Program p regs k a) (lib : Fin a → Macro Q Γ m g) :
    ∀ᶠ n : ℕ in atTop, ∀ (R teams t d link inner e w : ℕ) (M : Setup teams w p regs k a e)
      (G : Wiring R teams t d link inner n (Edge teams regs w e (w+1))),
      M.program = P → G.program = programPrefix (Processor.machine P lib) →
      ∀ pin ext team fuel, M.lib = macros lib fuel → max 1 (fuel-1) ≤ M.privateClock →
      RowDictionary M G lib pin ext team → G.value pin ext team = nativeValue M.machine M.limit.val M.cap.val M.privateClock := by
  filter_upwards [eventually_processor_witnesses P lib] with n compiled
  intro R teams t d link inner e w M G program header pin ext team fuel library clock dictionary
  subst P
  have b := dictionary.bijection fuel library clock
  have signed := compiled R teams t d link inner (Edge teams regs w e (w+1)) G header pin ext team
  refine signed.trans (Eq.trans ?_ b.sum_eq_native)
  apply Finset.sum_congr
  · ext s; simp only [Finset.mem_univ]
  · intro s _; rfl

end TeamContraction

end BorderVNP
end Computability
end OAI
