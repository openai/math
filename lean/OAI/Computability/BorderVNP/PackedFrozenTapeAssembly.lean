import OAI.Computability.BorderVNP.PackedFrozenTapeRows

/-! # Parallel child rectangles and chronological appends on the actual pins -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open ParseBatchSort VPVNP.VerifierNetwork Crossing
open scoped Classical

variable {R B R' B' σ : Type*} {d k : ℕ} (S : Schema R B) (T : Schema R' B')

/-- Parallel physical array. Old records and field-bit references keep their original
within-child order, and each child receives its own disjoint rectangle. -/
def Schema.parallel (k : ℕ) : Schema (Fin k × R) (Fin k × B) where
  rows := (List.finRange k).flatMap fun i => S.rows.map (i,·)
  tags z := S.tags z.2
  width z := S.width z.2
  pin z j u := (z.1,S.pin z.2 j u)

/-- Renaming between the parallel public rectangle's pins and the individual child arrays. -/
def parallelPin : Pins (Fin k × R) (Fin k × B) d → Fin k × Pins R B d
  | .inl (⟨i,r⟩,z) => (i,.inl (r,z))
  | .inr ⟨i,b⟩ => (i,.inr b)

/-- Restricting the parallel array to one owner is the concatenation of the
corresponding restrictions of its child rectangles, in chronological order. -/
theorem Schema.parallel_at (x : Fin k × Pins R B d → Bool) (key : ℕ) :
    (S.parallel k).atSite (x ∘ parallelPin) key =
      (List.finRange k).flatMap fun i => S.atSite (fun z => x (i,z)) key := by
  simp only [Schema.parallel,Schema.atSite,List.filterMap_flatMap,List.filterMap_map,Schema.read,owner,
    parallelPin,Function.comp_def]
  rfl

/-- Concatenate two physical row blocks. The first block's observation order
precedes the second, even when both contribute to a single site. -/
def Schema.append : Schema (R ⊕ R') (B ⊕ B') where
  rows := S.rows.map Sum.inl ++ T.rows.map Sum.inr
  tags := Sum.elim S.tags T.tags
  width := Sum.elim S.width T.width
  pin
    | .inl r,j,u => .inl (S.pin r j u)
    | .inr r,j,u => .inr (T.pin r j u)

/-- The chronological splice is a fixed relabeling of pins. -/
def appendPin : Pins (R ⊕ R') (B ⊕ B') d → Pins R B d ⊕ Pins R' B' d
  | .inl (.inl r,z) => .inl (.inl (r,z))
  | .inl (.inr r,z) => .inr (.inl (r,z))
  | .inr (.inl b) => .inl (.inr b)
  | .inr (.inr b) => .inr (.inr b)

/-- Source order at one site after the splice, including the row boundaries. -/
theorem Schema.append_at (x : Pins R B d → Bool) (y : Pins R' B' d → Bool) (key : ℕ) :
    (S.append T).atSite (Sum.elim x y ∘ appendPin) key = S.atSite x key ++ T.atSite y key := by
  simp only [Schema.append,Schema.atSite,List.filterMap_append,List.filterMap_map,Function.comp_def,
    Schema.read,owner,appendPin,Sum.elim_inl,Sum.elim_inr]
  rfl

variable [Fintype R] [Fintype B] [Fintype R'] [Fintype B'] [Fintype σ]

/-- Put a carried child pin array into the concrete parallel tape without a gate. -/
noncomputable def parallelFramePins (f : Frame σ (Fin k × Pins R B d)) : Frame σ (Pins (Fin k × R) (Fin k × B) d) :=
  f.select parallelPin

/-- Combine the physical emitters for two successive immutable blocks. -/
noncomputable def appendFrame (f : Frame σ (Pins R B d)) (g : Frame σ (Pins R' B' d)) :
    Frame σ (Pins (R ⊕ R') (B ⊕ B') d) := (parallelFrame f g).select appendPin

/-- No gate rewrites an existing row while assembling the two output blocks. -/
theorem appendFrame_size (f : Frame σ (Pins R B d)) (g : Frame σ (Pins R' B' d)) :
    (appendFrame f g).size = f.size+g.size := by simp [appendFrame]

/-- The executable chronological append gives exactly the two semantic row lists. -/
theorem appendFrame_at (f : Frame σ (Pins R B d)) (g : Frame σ (Pins R' B' d)) (x : σ → Bool) (key : ℕ) :
    (S.append T).atSite ((appendFrame f g).eval x) key = S.atSite (f.eval x) key ++ T.atSite (g.eval x) key := by
  have eval : (appendFrame f g).eval x = Sum.elim (f.eval x) (g.eval x) ∘ appendPin := by
    funext z
    rcases z with ⟨(r|r),j⟩ | (b|b) <;> simp [appendFrame,appendPin]
  rw [eval,S.append_at]

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
