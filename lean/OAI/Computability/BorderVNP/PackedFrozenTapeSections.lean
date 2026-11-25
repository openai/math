import OAI.Computability.BorderVNP.PackedFrozenTapeAssembly
import OAI.Computability.BorderVNP.PackedFrozenTapeRekey

/-! # Composing complete public record sections of the saved node -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open CellSparse ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {R B R' B' σ V : Type*} {d : ℕ} (S : Schema R B) (T : Schema R' B')

/-- A publicly addressed portion of a physical site's row list. Empty sections
are allowed; enabled records always name actual sites. -/
abbrev Schema.Section (x : Pins R B d → Bool) (id : V ↪ ℕ) (rows : V → List Record) : Prop :=
  S.Block x id fun v => (rows v).map marked

/-- A complete initial or retained public site tape is already a physical section. -/
theorem Schema.Image.toSection {x : Pins R B d → Bool} {id : V ↪ ℕ} {sites : V → Site}
    (h : S.Image x id sites) : S.Section x id (fun v => (sites v).rows) := ⟨h.owners,h.records⟩

/-- When the section's row list is the actual installed private program's directory,
the same public pins certify the complete tape at this node. -/
theorem Schema.Section.image {x : Pins R B d → Bool} {id : V ↪ ℕ} {rows : V → List Record}
    (h : S.Section x id rows) (sites : V → Site) (records : ∀ v, rows v = (sites v).rows) :
    S.Image x id sites := ⟨h.owners,fun v => (h.atSite v).trans (congrArg (List.map marked) (records v))⟩

/-- Chronological appends preserve both exact row lists and absence of active phantom owners. -/
theorem Schema.Section.append {x : Pins R B d → Bool} {y : Pins R' B' d → Bool} {id : V ↪ ℕ}
    {rows cols : V → List Record} (hx : S.Section x id rows) (hy : T.Section y id cols) :
    (S.append T).Section (Sum.elim x y ∘ appendPin) id (fun v => rows v ++ cols v) := by
  constructor
  · rintro (r|r) hr ha
    · have present : r ∈ S.rows := by simpa [Schema.append] using hr
      exact hx.owners r present ha
    · have present : r ∈ T.rows := by simpa [Schema.append] using hr
      exact hy.owners r present ha
  · intro v
    rw [S.append_at,hx.atSite,hy.atSite,List.map_append]

variable [Fintype R] [Fintype B] [Fintype R'] [Fintype B'] [Fintype σ]

/-- The actual Boolean append instruction realizes the concatenation of its two
verified source sections on exactly the same input assignment. -/
theorem appendFrame_section (f : Frame σ (Pins R B d)) (g : Frame σ (Pins R' B' d)) (x : σ → Bool)
    (id : V ↪ ℕ) (rows cols : V → List Record) (hf : S.Section (f.eval x) id rows) (hg : T.Section (g.eval x) id cols) :
    (S.append T).Section ((appendFrame f g).eval x) id (fun v => rows v ++ cols v) := by
  have eval : (appendFrame f g).eval x = Sum.elim (f.eval x) (g.eval x) ∘ appendPin := by
    funext z
    rcases z with ⟨(r|r),j⟩ | (b|b) <;> simp [appendFrame,appendPin]
  rw [eval]
  exact hf.append _ _ hg

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
