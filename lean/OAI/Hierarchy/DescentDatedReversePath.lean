import OAI.Hierarchy.DescentHaloPackedRebase
import OAI.Hierarchy.DescentHaloPackedGather

namespace OAI
/-! # The native reverse four-hop word is the canonical occupied parent socket -/
namespace Hierarchy.DescentHaloWalkRAM.Rebase
open DescentSharedCableNames DescentHaloPackedRebase
open scoped Classical
noncomputable section
variable {H D : ℕ} (R : Fin H→Fin D→Option (Fin H))
local notation "P" => breadth D

private theorem terminal_iff (v u : Fin H) (j : Fin P) :
    terminal R v j=u.val ↔ Gather.reaching R v j=some u := by
  cases read : walk R v (path j) 4 with
  | none =>
    have dead : H≠u.val:=Nat.ne_of_gt u.isLt
    simp [terminal,number,Gather.reaching,read,dead]
  | some x => simp [terminal,number,Gather.reaching,read,Fin.ext_iff]

private theorem choose_first (v u : Fin H) (q : Fin P) (found : terminal R v q=u.val)
    (absent : ∀j:Fin P,j<q→ terminal R v j≠u.val) (js : List (Fin P))
    (ordered : js.Pairwise (·<·)) (here_ : q∈js) : choose R v u js=some q := by
  induction js with
  | nil=>simp at here_
  | cons j js ih=>
    rcases List.mem_cons.mp here_ with eqn | later
    · subst j
      simp [choose,found]
    · have prior := List.pairwise_cons.mp ordered
      rw [choose,ite_eq_right (absent j (prior.1 q later))]
      exact ih prior.2 later

/-- A path from the donor back to the receiving site can have several reverse
walks. The paid rebase picks exactly the path whose local gather entry is live. -/
theorem canonical_path (v u : Fin H) (p q : Fin P) (forward : walk R v (path p) 4=some u)
    (issued : Gather.select (Gather.reaching R) u q=some v) :
    value R .path v p=q.val := by
  unfold Gather.select at issued
  split at issued
  · contradiction
  · rename_i first_
    have eqn:terminal R u q=v.val:=(terminal_iff R u v q).2 issued
    have absent (j : Fin P) (lt : j<q) : terminal R u j≠v.val := by
      intro hit
      exact first_ ⟨j,lt,((terminal_iff R u v j).1 hit).trans issued.symm⟩
    have chose:=choose_first R u v q eqn absent (List.finRange P) (List.pairwise_lt_finRange P) (List.mem_finRange q)
    simp [value,forward,chose,slot]

theorem packed_path (v u : Fin H) (p q : Fin P) (forward : walk R v (path p) 4=some u)
    (issued : Gather.select (Gather.reaching R) u q=some v) :
    fetch P (digest (digit R .path v)) (Packed.token (some p))=Packed.token (some q) :=
  fetch_at _ _ _ (canonical_path R v u p q forward issued)

end
end Hierarchy.DescentHaloWalkRAM.Rebase

end OAI
