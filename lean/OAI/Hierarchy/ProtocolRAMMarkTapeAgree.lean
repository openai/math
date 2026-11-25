import OAI.Hierarchy.ProtocolRAMMarkLoad
import OAI.Hierarchy.ProtocolRAMBelow

namespace OAI
/-! # Agreement of the full native mark-tape output below a cutoff -/
namespace Hierarchy.ProtocolRAM.MarkTape
open Computability.VPVNP.BurstRAM PrivateRAM Calendar
open scoped Fin.CommRing
variable {w cut : ℕ} {m n : Memory w}

theorem Gate.apply_below (g : Gate) (same : Below cut m n)
    (left : g.lhs< cut) (right : g.rhs< cut) : Below cut (g.apply m) (g.apply n) := by
  intro a ha
  by_cases hit : a=g.dst
  · subst a
    simp only [Gate.apply,Function.update_self,same _ left,same _ right]
  · simpa only [Gate.apply,Function.update_of_ne hit] using same a ha

theorem eval_below (same : Below cut m n) (gs : List Gate)
    (reads : ∀g∈gs,g.lhs< cut ∧ g.rhs< cut) : Below cut (eval gs m) (eval gs n) := by
  induction gs generalizing m n with
  | nil => exact same
  | cons g rest ih =>
    have both := reads g (List.mem_cons_self ..)
    exact ih (g.apply_below same both.1 both.2) (fun v hv=>reads v (List.mem_cons_of_mem g hv))

theorem loaded_below_agree (same : Below cut m n) (tiles work first count : ℕ)
    (marks : Bank) (fit : marks.Fits w work) (before : work≤ cut) :
    Below cut (loaded tiles work first count marks m) (loaded tiles work first count marks n) := by
  apply same.scan work (4+tiles+first+count) (loadTerm tiles marks) _ before
  exact ⟨trivial,trivial,trivial,⟨trivial,trivial,⟨fit,trivial,trivial⟩,trivial⟩⟩

/-- This compares every word below the cutoff, including all transient NAND
registers, residual inventory and candidate results of the ordered scan. -/
theorem load_run_below (same : Below cut m n) (tiles work first : ℕ)
    (ps : List (List (Fin tiles))) (marks : Bank) (fit : marks.Fits w work)
    (before : work+4+tiles+first+ps.length≤ cut) :
    let gates := compilePaths tiles work first ps
    Below cut (eval gates (loaded tiles work first ps.length marks m))
      (eval gates (loaded tiles work first ps.length marks n)) := by
  apply eval_below (loaded_below_agree same tiles work first ps.length marks fit (by omega))
  intro g hg
  have span := addresses tiles work first ps g hg
  exact ⟨span.2.1.trans_le before,span.2.2.2.1.trans_le before⟩

end Hierarchy.ProtocolRAM.MarkTape

end OAI
