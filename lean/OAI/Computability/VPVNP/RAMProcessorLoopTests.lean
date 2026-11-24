import OAI.Computability.VPVNP.RAMProcessorGraphRuns

/-! # Physical dispatch of the bucket entry, loop, and final checks -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM

variable {w p r k : ℕ}

private theorem test_run (T : Template p r k) (s : Snapshot w p r k) (l : Label p r)
    (tree : SiteTests.Tree) (next : SiteTests.Exit → Label p r)
    (hblock : blocks T l = (tree.fragment next).onPorts testPorts) :
    StackRuns (table T) (tree.ticks s.tests + (tree.eval s.tests).bits.length)
      (atLabel T l) s.bank (atLabel T (next (tree.eval s.tests))) s.bank := by
  apply ProcessorFlow.run (blocks := blocks T) (l := l)
  rw [hblock]
  exact Fragment.runs_framed testPorts_injective (tree.fragment_runs next s.tests)
    s.test_at s.test_at (fun _ _ => rfl)

private theorem exit_length_le (e : SiteTests.Exit) : e.bits.length ≤ 2 := by cases e <;> decide

theorem checkEntry_run (T : Template p r k) (s : Snapshot w p r k) :
    ∃ n ≤ 60*w+41, StackRuns (table T) n (atLabel T .checkEntry) s.bank
      (atLabel T (route true (SiteTests.entry.eval s.tests))) s.bank := by
  have h := SiteTests.entry_work s.tests
  have hl := exit_length_le (SiteTests.entry.eval s.tests)
  exact ⟨_, by omega, test_run T s .checkEntry SiteTests.entry (route true) rfl⟩

theorem iteration_run (T : Template p r k) (s : Snapshot w p r k) :
    ∃ n ≤ 40*w+30, StackRuns (table T) n (atLabel T .iteration) s.bank
      (atLabel T (route false (SiteTests.iteration.eval s.tests))) s.bank := by
  have h := SiteTests.iteration_work s.tests
  have hl := exit_length_le (SiteTests.iteration.eval s.tests)
  exact ⟨_, by omega, test_run T s .iteration SiteTests.iteration (route false) rfl⟩

theorem finalCheck_run (T : Template p r k) (s : Snapshot w p r k) :
    ∃ n ≤ 40*w+42, StackRuns (table T) n (atLabel T .finalCheck) s.bank
      (atLabel T (if SiteTests.finalCheck.eval s.tests = .finish then .close else .reject)) s.bank := by
  have h := SiteTests.final_work s.tests
  have hl := exit_length_le (SiteTests.finalCheck.eval s.tests)
  exact ⟨_, by omega, test_run T s .finalCheck SiteTests.finalCheck _ rfl⟩

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
