import OAI.Computability.BorderVNP.FiniteProcessorWeightRun
import OAI.Computability.BorderVNP.FiniteProductReplay
import OAI.Computability.BorderVNP.FiniteTeamReplayValue
import OAI.Computability.BorderVNP.TeamContractionNative

/-! # The field processor contraction over the original signed branch tapes

All interface wires, instructions, local replay strings and site clock limits
are unchanged by the finite field accumulator. Each original accepting leaf is
assigned the exact terminal field output of its unique instrumented replay.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape TeamSite TeamContraction UniversalMachine Filter
open scoped BigOperators Classical

variable {Q Γ : Type} [Fintype Q] {p r k a m g : ℕ} {F : Type*} [Field F] [Fintype F]
variable {R batch t d link inner n : ℕ} {Edge : Type}

/-- Weight of one actual original signed physical leaf under the finite-field processor. -/
noncomputable def leafValue (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (w : Returns Q Γ F m a) (G : Wiring R batch t d link inner n Edge) (pin : Fin d → Bool)
    (ext : Exterior R batch link → Bool) (int : Edge → Bool) (team : Fin (R+1)) (j : Fin batch)
    (x : ↥(TeamContraction.physicalLeaves G TeamSite.Layout.input (Processor.code P lib) Processor.negative
      Processor.start 36 pin ext int team j)) : F :=
  ((FieldStack.leafEquiv (Processor.code P lib) (factor lib w) terminal Processor.negative (n^36)
    Processor.start (StackCompiler.labeledInput TeamSite.Layout.input (G.input pin ext int team j)) 1) x).val.2

/-- With its own true field prefix, the actual team contraction sums exactly the
same accepted original branch tapes, weighted by their instrumented outputs. -/
theorem eventually_contraction (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (w : Returns Q Γ F m a) :
    ∀ᶠ n : ℕ in atTop, ∀ (R batch t d link inner : ℕ) (Edge : Type) [Fintype Edge]
      (G : Wiring R batch t d link inner n Edge), G.program = programPrefix (machine P lib w) →
      ∀ pin, FieldTeam.fieldContraction G F pin =
        ∑ ext : Exterior R batch link → Bool, ∏ team : Fin (R+1), ∑ int : Edge → Bool,
          ∑ leaves : (j : Fin batch) → ↥(TeamContraction.physicalLeaves G TeamSite.Layout.input
            (Processor.code P lib) Processor.negative Processor.start 36 pin ext int team j),
            ∏ j, leafValue P lib w G pin ext int team j (leaves j) := by
  filter_upwards [FieldTeam.eventually_replay_contraction TeamSite.Layout.input 36 (by decide) (by decide)
    (code P lib w) (FieldStack.productOutput (factor lib w) terminal) (Processor.start,Fintype.equivFin F 1)] with n h
  intro R batch t d link inner Edge _ G hg pin
  rw [h _ _ _ _ _ _ _ G hg]
  apply Finset.sum_congr rfl
  intro ext _
  apply Finset.prod_congr rfl
  intro team _
  apply Finset.sum_congr rfl
  intro int _
  let E := Equiv.piCongrRight (fun j : Fin batch => FieldStack.leafEquiv (Processor.code P lib) (factor lib w)
    terminal Processor.negative (n^36) Processor.start
    (StackCompiler.labeledInput TeamSite.Layout.input (G.input pin ext int team j)) 1)
  exact (E.sum_comp (fun xs => ∏ j, (xs j).val.2)).symm

end FieldProcessor

end BorderVNP
end Computability
end OAI
