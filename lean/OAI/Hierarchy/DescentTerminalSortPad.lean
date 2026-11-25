import OAI.Hierarchy.TaggedSortLiftStage
import OAI.Hierarchy.TaggedSortLiftPadRows
import OAI.Hierarchy.DescentTerminalShortSort
import Mathlib.Data.Finset.Max

namespace OAI
/-! # Filling the unused suffix of each short-sort block with a fixed top record -/

namespace Hierarchy.Tagged.TerminalSort
open ThreeFlat Routing SortNetwork
open scoped Classical
noncomputable section

def key {d w : ℕ} (digit : Fin d→Fin w) (row : Fin w→Bool) := addressEquiv d (row ∘ digit)

private theorem hasTop {w d : ℕ} (digit : Fin d→Fin w) : ∃ v, ∀r,key digit r≤key digit v := by
  obtain ⟨v,_,greatest⟩ := Finset.exists_max_image Finset.univ (key digit) Finset.univ_nonempty
  exact ⟨v,fun r=>greatest r (Finset.mem_univ _)⟩

def sentinel {w d : ℕ} (digit : Fin d→Fin w) := Classical.choose (hasTop digit)

theorem sorted_pad {d w n t : ℕ} (digit : Fin d→Fin w) (room : t≤2^n) (x : Fin t→Fin w→Bool) :
    sorted digit (pad (sentinel digit) x : Records n w) =
      pad (sentinel digit) (x ∘ Tuple.sort (key digit ∘ x)) :=
  sort_pad room _ _ (Classical.choose_spec (hasTop digit)) x

end
end Hierarchy.Tagged.TerminalSort

end OAI
