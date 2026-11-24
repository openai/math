import OAI.Computability.VPVNP.RAMProcessorSiteTests
import OAI.Computability.VPVNP.RAMProcessorFlow

/-!
# Typed exits of the site checks

The graph consumes the verdict stack before transferring to the selected
caller label. The caller receives all original site data and empty scratch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteTests

variable {L : Type} {w : ℕ}

/-- Compile the site's decision tree into a graph fragment that consumes its verdict bits and
jumps to the caller's reject, finish or dispatch label. -/
def Tree.fragment (tree : Tree) (next : Exit → L) : Fragment Port L where
  State := tree.machine.State ⊕ Bool
  entry := .inl tree.machine.body.entry
  code
    | .inl q => (tree.machine.body.code q).rename id fun r => .inl (r.elim (.inr false) Sum.inl)
    | .inr false => .pop .verdict fun
      | some true => .inl (.inr true)
      | _ => .inr (next .reject)
    | .inr true => .pop .verdict fun
      | some true => .inr (next .dispatch)
      | some false => .inr (next .finish)
      | none => .inr (next .reject)

private theorem decodeRun (tree : Tree) (next : Exit → L) (e : Exit) (s : Snapshot w) :
    StackRuns (tree.fragment next).isolated e.bits.length (.inl (.inr false))
      (Function.update s.bank .verdict e.bits) (.inr (next e)) s.bank := by
  have endBank : Function.update s.bank .verdict [] = s.bank := Function.update_eq_self _ _
  cases e <;> (
    refine .cons (.pop rfl) ?_
    simp only [Function.update_self, Function.update_idem, Exit.bits, List.head?_cons,
      List.tail_cons, endBank]
    first | exact .nil .. | (refine .cons (.pop rfl) ?_; simp only [Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons, endBank]; exact .nil ..))

theorem Tree.fragment_runs (tree : Tree) (next : Exit → L) (s : Snapshot w) :
    (tree.fragment next).Runs (tree.ticks s + (tree.eval s).bits.length) s.bank
      (next (tree.eval s)) s.bank := by
  let f := tree.fragment next
  let labels : Option tree.machine.State → f.State ⊕ L := fun r => .inl (r.elim (.inr false) Sum.inl)
  have rows (q : Option tree.machine.State) (hq : (tree.machine.body.standalone q).returns = false) :
      f.isolated (labels q) = (tree.machine.body.standalone q).rename id labels := by
    cases q with
    | none => contradiction
    | some q => rfl
  have same (u : Stacks Port) : installStacks id s.bank u = u := by
    funext j
    exact installStacks_at Function.injective_id _ _ j
  have run := (tree.run s).lift id Function.injective_id labels s.bank rows
  rw [same, same] at run
  exact run.trans (decodeRun tree next (tree.eval s) s)

end RAMTape.SiteTests

end VPVNP
end Computability
end OAI
