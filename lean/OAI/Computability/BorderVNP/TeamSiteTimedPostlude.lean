import OAI.Computability.BorderVNP.TeamSiteTimedRowModel
import OAI.Computability.BorderVNP.TeamSiteTimedInstalled

/-! # Transport of the physical frame checks and sorter after a timed RAM block -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP RAMTape BurstRAM TeamPrivateFragment TrustedClock
open private all_successors successor_rename step_next step_lift_row from OAI.Computability.BorderVNP.TeamSiteClockPhases

variable {Q Γ : Type} {p r k a m g : ℕ}
variable (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (mark : Fin a → Γ)
local notation "old" => Processor.code P (fun j => extend (lib j) (mark j))
local notation "Full" => Stacks (TeamClocked.Port (Layout.Port r k ((m+1)*g)))

/-- Every processor phase reachable after the RAM exits to its outgoing frame. -/
def postlude : Processor.Label P Q (m+1) g → Prop
  | .block (.loop _ (.close ..)) | .block (.finish ..) | .block (.done _) | .block .invalid |
    .close .. | .sort .. | .reject => True
  | _ => False

private theorem finish_post (sg : Option Bool) (ok : Bool) :
    postlude (m:=m) (g:=g) P (.block (Endpoint.finishLabel (Q:=Q) sg ok)) := by
  cases ok <;> trivial

private theorem post_step (q : Processor.Label P Q (m+1) g) (post : postlude P q) :
    successors (postlude P) (old q) := by
  cases q with
  | block ep =>
    cases ep with
    | loop last x => cases x <;> first | contradiction | trivial
    | finish sg x =>
      rw [Processor.code,successor_rename] <;> try (intro z eq; cases eq)
      cases x <;> simp only [Endpoint.code] <;> first | apply finish_post | exact all_successors _ _ (fun _ => by trivial) _
    | done | invalid => trivial
    | startup => contradiction
  | close sg x =>
    apply all_successors
    rintro (_|_) <;> trivial
  | sort sg x => apply all_successors; intro; trivial
  | reject => trivial
  | _ => contradiction

private theorem replay_successors {K S : Type} (good : S → Prop) (op : StackOp K S) (bits : List Bool)
    (h : successors good op) :
    successors (fun z : S × List Bool => good z.1)
      (match op with
       | .choose l r => match bits with | [] => .halt false | b::bs => .goto ((if b then r else l),bs)
       | instr => instr.rename id (fun s => (s,bits))) := by
  cases op <;> first | exact h | (cases bits with | nil => trivial | cons b bs => cases b <;> first | exact h.1 | exact h.2)

/-- The real frame comparison, record closure and both virtual sort lanes can run
unchanged after a native timeout. The enclosing template and clock are preserved. -/
theorem postlude_run {t q bits s q' rest s'} (path : StackRuns (replay old) t (q,bits) s (q',rest) s')
    (start : postlude P q) (outer : Full) :
    StackRuns (replay (code P lib mark)) t (.site q,bits) (installStacks TeamClocked.Port.user outer s)
      (.site q',rest) (installStacks TeamClocked.Port.user outer s') := by
  let ports := TeamClocked.Port.user (K := Layout.Port r k ((m+1)*g))
  have inj : Function.Injective ports := fun _ _ => TeamClocked.Port.user.inj
  let labels := fun z : Processor.Label P Q (m+1) g × List Bool => (Label.site (m:=m) z.1,z.2)
  have all {t : ℕ} {z z' : Processor.Label P Q (m+1) g × List Bool} {b b'}
      (run : StackRuns (replay old) t z b z' b') (late : postlude P z.1) :
      StackRuns (replay (code P lib mark)) t (labels z) (installStacks ports outer b)
        (labels z') (installStacks ports outer b') := by
    induction run with
    | nil => exact .nil ..
    | @cons z b u v z' b' t step tail ih =>
      have nxt := step_next step (replay_successors (postlude P) (old z.1) z.2 (post_step P lib mark z.1 late))
      apply StackRuns.cons _ (ih nxt)
      apply step_lift_row step ports inj labels outer
      obtain ⟨q,bs⟩ := z
      have row := site_row P lib mark q fun last sg j pc eq => by subst q; exact late
      dsimp only [labels]
      rw [replay,row,replay]
      cases h : old q <;> simp only [StackOp.rename,Function.comp_def,id_eq,ports]
      cases bs <;> simp; split <;> rfl
  exact all path start

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
