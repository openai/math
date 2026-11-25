import OAI.Computability.BorderVNP.TeamContractionNative
import OAI.Computability.BorderVNP.TeamContractionPaths
import OAI.Computability.BorderVNP.TeamSiteProcessor

/-! # Signed contraction of the actual compiled team processor

The universal coefficients on the actual slot layout expand as a sum over the
true shared links and independent accepted finite replay scripts of the complete
processor table. Zero-weight native RAM executions may be discarded exactly.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP RAMTape UniversalMachine Diagonal
open scoped BigOperators Classical

variable {R r t d link inner n p regs pub a m g : ℕ} {Edge Q Γ : Type}

/-- Genuine accepting replay choices at all processors of a team on one common physical
assignment, for the compiled initialization, endpoint, record closure and sorting table. -/
abbrev SiteWitness (G : Wiring R r t d link inner n Edge) (P : TeamOpcode.Program p regs pub a)
    (lib : Fin a → TeamSite.Macro Q Γ m g) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (team : Fin (R+1)) :=
  Σ int : Edge → Bool, (j : Fin r) → ↥(physicalLeaves G TeamSite.Layout.input
    (TeamSite.Processor.code P lib) TeamSite.Processor.negative TeamSite.Processor.start 36 pin ext int team j)

/-- Product of the actual signed terminal values at every processor, after all physical
checks pass. -/
def siteWeight {G : Wiring R r t d link inner n Edge} {P : TeamOpcode.Program p regs pub a}
    {lib : Fin a → TeamSite.Macro Q Γ m g} {pin ext team} (z : SiteWitness G P lib pin ext team) : ℤ :=
  ∏ j, TeamTape.haltWeight true (z.2 j).val.2

/-- An accepting physical leaf always has sign one or minus one, even when the RAM model
also permits a valid branch with absorbed zero weight. -/
theorem siteWeight_ne_zero {G : Wiring R r t d link inner n Edge} {P : TeamOpcode.Program p regs pub a}
    {lib : Fin a → TeamSite.Macro Q Γ m g} {pin ext team} (z : SiteWitness G P lib pin ext team) : siteWeight z ≠ 0 := by
  unfold siteWeight
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  cases (z.2 j).val.2 <;> decide

/-- One length threshold gives the actual signed finite-witness sum simultaneously on
every team, for the complete site processor's fixed literal program. -/
theorem eventually_processor_witnesses [Fintype Q] (P : TeamOpcode.Program p regs pub a)
    (lib : Fin a → TeamSite.Macro Q Γ m g) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (R r t d link inner : ℕ) (Edge : Type) [Fintype Edge]
      (G : Wiring R r t d link inner n Edge),
      G.program = programPrefix (TeamSite.Processor.machine P lib) →
      ∀ pin ext team, G.value pin ext team = ∑ z : SiteWitness G P lib pin ext team, siteWeight z := by
  filter_upwards [eventually_replay_value TeamSite.Layout.input 36 (by decide) (by decide)
    (TeamSite.Processor.code P lib) TeamSite.Processor.negative TeamSite.Processor.start] with n he
  intro R r t d link inner Edge _ G h pin ext team
  exact (he R r t d link inner Edge G h pin ext team).trans (Fintype.sum_sigma' _).symm

/-- The full paper contraction over actual raw wire bits splits into true external
transmissions and one signed product of finite machine leaves per team. -/
theorem eventually_processor_contraction [Fintype Q] (P : TeamOpcode.Program p regs pub a)
    (lib : Fin a → TeamSite.Macro Q Γ m g) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (R r t d link inner : ℕ) (Edge : Type) [Fintype Edge]
      (G : Wiring R r t d link inner n Edge),
      G.program = programPrefix (TeamSite.Processor.machine P lib) →
      ∀ pin, signedContraction G.slot pin =
        ∑ ext, ∏ team, ∑ z : SiteWitness G P lib pin ext team, siteWeight z := by
  filter_upwards [eventually_processor_witnesses P lib] with n he
  intro R r t d link inner Edge _ G h pin
  rw [G.contraction_eq]
  exact Finset.sum_congr rfl fun ext _ => Finset.prod_congr rfl fun team _ => he R r t d link inner Edge G h pin ext team

/-- Genuine native accepting paths of nonzero weight, retaining exact branch scripts,
all executed instructions and true old words. -/
abbrev NonzeroPath {w : ℕ} {S : Type*} (M : MachineInput w S) (ticks burst privateClock : ℕ) :=
  {p : NativePath M ticks burst privateClock // pathWeight p.val ≠ 0}

/-- Removing the genuine zero-weight paths gives exactly the same native integer signed
count. This is the source-side indexing used when matching actual accepting U* leaves. -/
theorem nativeValue_nonzero {w : ℕ} {S : Type*} (M : MachineInput w S) (ticks burst privateClock : ℕ) :
    letI := Fintype.ofFinite (NativePath M ticks burst privateClock)
    nativeValue M ticks burst privateClock = ∑ p : NonzeroPath M ticks burst privateClock, pathWeight p.val.val := by
  let := Fintype.ofFinite (NativePath M ticks burst privateClock)
  unfold nativeValue
  have he := Fintype.sum_subtype_add_sum_subtype (fun p : NativePath M ticks burst privateClock => pathWeight p.val ≠ 0)
    (fun p => pathWeight p.val)
  rw [← he]
  exact add_eq_left.mpr (Finset.sum_eq_zero fun p _ => not_ne_iff.mp p.property)

end TeamContraction

end BorderVNP
end Computability
end OAI
