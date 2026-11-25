import OAI.Computability.BorderVNP.FiniteTeamContraction
import OAI.Computability.BorderVNP.FiniteTeamReplay

/-! # Exact field sums over physical team replay leaves

Each team assignment supplies a different input word to every copy of the fixed
validator. Its value is the sum over actual binary executions of those copies.
The common exterior assignment is chosen once for the entire contraction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldTeam

open TeamContraction VPVNP.RAMTape VPVNP.UniversalMachine Filter
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] {K Q : Type} [DecidableEq K] [Fintype K] [Fintype Q]
variable {R r t d link inner n : ℕ} {Edge : Type}

/-- Accepting executions at one literal site. Their keys are the exact consumed
choices and their values come from the actual terminal labels. -/
def physicalLeaves (G : Wiring R r t d link inner n Edge) (input : K) (C : StackCode K Q)
    (w : Q → F) (start : Q) (u : ℕ) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (int : Edge → Bool) (team : Fin (R+1)) (j : Fin r) : Finset (List Bool × F) :=
  FieldReplay.leaves C w (n^u) start (StackCompiler.labeledInput input (G.input pin ext int team j))

/-- Expanding each processor by its exact accepting executions introduces one
independent choice tape per processor and one interior assignment per team. -/
theorem eventually_replay_value (input : K) (u : ℕ) (hu : 1 ≤ u) (clock : 2*(u+2)+1 ≤ 100)
    (C : StackCode K Q) (w : Q → F) (start : Q) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r t d link inner : ℕ) (Edge : Type) [Fintype Edge]
      (G : Wiring R r t d link inner n Edge),
      G.program = programPrefix (FieldStack.clockedMachine input u C w start) →
      ∀ pin ext team, fieldValue G F pin ext team =
        ∑ int : Edge → Bool,
          ∑ leaves : (j : Fin r) → ↥(physicalLeaves G input C w start u pin ext int team j),
            ∏ j, (leaves j).val.2 := by
  filter_upwards [eventually_site_value input u hu clock C w start] with n hsite
  intro R r t d link inner Edge _ G hG pin ext team
  unfold fieldValue
  apply Finset.sum_congr rfl
  intro int _
  refine Eq.trans ?_ (Fintype.prod_sum (fun j (z : ↥(physicalLeaves G input C w start u pin ext int team j)) =>
    z.val.2))
  apply Finset.prod_congr rfl
  intro j _
  rw [hsite _ _ _ _ _ _ _ G hG, FieldReplay.paths_eq_sum]
  exact (Finset.sum_coe_sort (physicalLeaves ..) Prod.snd).symm

/-- The whole wired network sums once over common exterior bits and, at each team,
sums all interior settings and their genuine accepting replay tuples. -/
theorem eventually_replay_contraction (input : K) (u : ℕ) (hu : 1 ≤ u) (clock : 2*(u+2)+1 ≤ 100)
    (C : StackCode K Q) (w : Q → F) (start : Q) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r t d link inner : ℕ) (Edge : Type) [Fintype Edge]
      (G : Wiring R r t d link inner n Edge),
      G.program = programPrefix (FieldStack.clockedMachine input u C w start) →
      ∀ pin, fieldContraction G F pin =
        ∑ ext : Exterior R r link → Bool, ∏ team : Fin (R+1),
          ∑ int : Edge → Bool,
            ∑ leaves : (j : Fin r) → ↥(physicalLeaves G input C w start u pin ext int team j),
              ∏ j, (leaves j).val.2 := by
  filter_upwards [eventually_replay_value input u hu clock C w start] with n teamValue
  intro R r t d link inner Edge _ G hG pin
  rw [fieldContraction_eq]
  exact Finset.sum_congr rfl fun ext _ => Finset.prod_congr rfl fun team _ =>
    teamValue _ _ _ _ _ _ _ G hG pin ext team

end FieldTeam

end BorderVNP
end Computability
end OAI
