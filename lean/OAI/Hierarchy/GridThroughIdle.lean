import OAI.Hierarchy.GridThroughSelect

namespace OAI
/-! # The physical identity setting on a legal system of rail lines -/

namespace Hierarchy.GridThrough.Program
open GridLens
noncomputable section

variable {E : Type} [Fintype E] [LinearOrder E] {k n p : ℕ} {width : Fin k → ℕ}

omit [LinearOrder E] in
/-- Erasing touches frees all previously reserved catalyst passages. -/
theorem idle_capacity (P : GridThrough.Program E n p width) (x : Cell k n) (j : Fin k) :
    width j ≤ (untouchedRails P.direction P.row (fun _ => none) x j).card := by
  let f (i : Fin (width j)) : (untouchedRails P.direction P.row (fun _ => none) x j) :=
    ⟨P.pass x ⟨j,i⟩, by
      apply Finset.mem_filter.mpr
      have axis := P.pass_dir x ⟨j,i⟩
      refine ⟨Finset.mem_univ _, axis, ?_, by simp⟩
      simpa only [axis] using P.pass_line x ⟨j,i⟩⟩
  have inj : Function.Injective f := by
    intro i i' h
    have h' : (Sigma.mk j i : Catalyst.Wire width) = ⟨j,i'⟩ :=
      P.pass_injective x (congrArg Subtype.val h)
    simpa using h'
  simpa using Fintype.card_le_of_injective f inj

/-- All pin values are literals. Canonical first-label catalyst reservations are
recomputed on the unchanged rail lines, now with every passage untouched. -/
def idle (P : GridThrough.Program E n p width) (literal : Cell k n → Fin p → Bool) :
    GridThrough.Program E n p width :=
  ofUntouched P.direction P.row (fun _ => none) width P.idle_capacity
    (fun c i => .inr (literal c i))
    (fun _ _ _ h => by cases h) (fun u => by cases u.1.property)

@[simp] theorem idle_touch (P : GridThrough.Program E n p width) (literal : Cell k n → Fin p → Bool)
    (e : E) : (P.idle literal).touch e = none := rfl

@[simp] theorem idle_dataBits (P : GridThrough.Program E n p width) (literal : Cell k n → Fin p → Bool)
    (x : GridDiagonal.Pins E) (c : Cell k n) : (P.idle literal).dataBits x c = literal c := rfl

/-- On every pair of exterior assignments the programmed setting evaluates to the identity. -/
theorem idle_eval {F : Type*} [Field F] (P : GridThrough.Program E n p width)
    (literal : Cell k n → Fin p → Bool) (f : (Fin p → Bool) → F)
    (units : ∀ c, f (literal c) = 1) (x : GridDiagonal.Pins E) :
    (P.idle literal).wiring.eval (Catalyst.ideal width f) x = GridDiagonal.identity F x :=
  (P.idle literal).eval_identity f (P.idle_touch literal) units x

end
end Hierarchy.GridThrough.Program

end OAI
