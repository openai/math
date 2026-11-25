import OAI.Hierarchy.DescentPhysicalDateHistory

namespace OAI
/-! # A single fixed instruction sequence on all named cuts of every ballot -/
namespace Hierarchy.DescentSixParty.Chronology.DateCode
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
open scoped Classical
variable {w : ℕ} (Cut : ℕ→Type*) (code : ∀i,Cut i→DateCode w)

/-- An unreachable date executes an empty four-tick row scan. Every reachable
date uses one opcode sequence independently of which ballot led to its cut. -/
def fromCuts (i : ℕ) : DateCode w :=
  if h : Nonempty (Cut i) then code i (Classical.choice h) else .reset (scan w 0 0 .row) 4

theorem fromCuts_at (fixed : ∀i,∀x y : Cut i,code i x=code i y) (i : ℕ) (x : Cut i) :
    fromCuts Cut code i=code i x :=by
  rw [fromCuts,dite_eq_left (show Nonempty (Cut i) from ⟨x⟩)]
  exact fixed i _ x

theorem fromCuts_total (all : ∀i,∀x:Cut i,∀m,∃out,(code i x).Runs m out)
    (i : ℕ) (m : Memory w) : ∃out,(fromCuts Cut code i).Runs m out :=by
  unfold fromCuts
  split
  · exact all i _ m
  · refine ⟨image 0 0 .row m,?_⟩
    exact @scan_exec w 0 0 .row m trivial (by simp)

theorem fromCuts_cheap (all : ∀i,∀x:Cut i,(code i x).cheap) (i : ℕ) :
    (fromCuts Cut code i).cheap :=by
  unfold fromCuts
  split
  · exact all i _
  · exact scan_cheap w 0 0 .row

/-- Two physical executions at the same cut have the unique native postmemory.
Consequently each original local read and its successor's earlier-bank frame are
facts about the same public history memory used on malformed ballots. -/
theorem fromCuts_event (fixed : ∀i,∀x y : Cut i,code i x=code i y)
    (i : ℕ) (x : Cut i) (initial : Memory w) (Q : Memory w→Prop)
    (event : ∃out,(code i x).Runs (history (fromCuts Cut code) initial i) out ∧ Q out) :
    Q (history (fromCuts Cut code) initial (i+1)) :=by
  apply history_event
  rwa [fromCuts_at Cut code fixed i x]

end
end Hierarchy.DescentSixParty.Chronology.DateCode

end OAI
