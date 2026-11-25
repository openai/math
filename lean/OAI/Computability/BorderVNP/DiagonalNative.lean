import OAI.Computability.BorderVNP.DiagonalSubstitution
import OAI.Computability.BorderVNP.TeamClockedProgram

/-!
# The physical program in the signed contraction

Fix one validator before choosing the processor length. Its prefix occupies
actual literal slots. The remaining slots may encode site descriptions,
residue advice, pin indices, links, or unused zero fields. The same eventual
length threshold covers every choice of these bits and every processor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP.RAMTape VPVNP.UniversalMachine Filter
open scoped BigOperators Classical

variable {Port State : Type} [DecidableEq Port] [Fintype Port] [Fintype State]

/-- Every site in the physical contraction uses the same literal code.
The processor threshold is chosen before the number of sites, link layout,
program data and live pin. The decoded runs include their own prefixes. -/
theorem eventually_native_contraction (input : Port) (u : ℕ) (hu : 1 ≤ u)
    (hclock : 2 * (u + 2) + 1 ≤ 100) (code : StackCode Port State)
    (negative : State → Bool) (start : State) :
    let program := TeamClocked.machine input u code negative start
    ∀ᶠ n : ℕ in atTop, ∀ (Pin Wire Proc : Type) [Fintype Wire] [Fintype Proc]
      (layout : Proc → Fin n → InputSlot Pin Wire)
      (tails : Proc → List (InputSlot Pin Wire)),
      (∀ s, List.ofFn (layout s) =
        (programPrefix program).map InputSlot.literal ++ tails s) →
      ∀ pins, signedContraction layout pins =
        ∑ links, ∏ s, TeamStack.paths code negative (n ^ u) start
          (StackCompiler.labeledInput input
            (programPrefix program ++ (tails s).map (InputSlot.read pins links))) := by
  intro program
  filter_upwards [TeamClocked.eventually_prefix_value input u hu hclock code negative start]
    with n compiled
  intro Pin Wire Proc _ _ layout tails hprefix pins
  refine Finset.sum_congr rfl fun links _ => Finset.prod_congr rfl fun s _ => ?_
  let word := fun j => (layout s j).read pins links
  have hraw : List.ofFn word = programPrefix program ++ (tails s).map (InputSlot.read pins links) := by
    change List.ofFn (InputSlot.read pins links ∘ layout s) = _
    rw [← List.map_ofFn, hprefix s, List.map_append, List.map_map]
    simp [InputSlot.read, Function.comp_def]
  have len := congrArg List.length hraw.symm
  rw [List.length_ofFn] at len
  have h := compiled ((tails s).map (InputSlot.read pins links)) len
  change signedCount word = _
  rw [← hraw] at h ⊢
  change signedCount (List.ofFn word).get = _ at h
  simpa only [signedCount, List.ofFn_get, List.length_ofFn, List.get_ofFn, Fin.cast_cast,
    Fin.cast_eq_self] using h

end Diagonal

end BorderVNP
end Computability
end OAI
