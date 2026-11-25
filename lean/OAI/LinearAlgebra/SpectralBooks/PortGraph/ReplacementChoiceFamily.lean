import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoices

/-! # Term choices on isomorphism classes of certified maps -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.ReplacementChoices.System

universe u

variable {N K : ℕ} {ε : ℝ} (C : System N K ε) (Term : Checked N K ε → Type u)
  {A B : MapRep N}

private def moveChoices (f : A.map.Iso B.map)
    (a : ∀ j, Term (C.checked A j)) (j : C.Occ B) : Term (C.checked B j) :=
  cast (congrArg Term (C.checked_iso f ((C.occEquiv f).symm j)))
    (a ((C.occEquiv f).symm j))

/-- Each occurrence chooses one term from the catalogue for its checked record. -/
def family : DecoratedMaps.Family N where
  Label M := ∀ j, Term (C.checked M j)
  move f :=
    { toFun := C.moveChoices Term f
      invFun := C.moveChoices Term f.symm
      left_inv a := by funext j; simp only [moveChoices, cast_cast]; rfl
      right_inv a := by funext j; simp only [moveChoices, cast_cast]; rfl }
  move_refl A a := by funext j; rfl
  move_trans f g a := by
    funext j
    change C.moveChoices Term (f.trans g) a j = C.moveChoices Term g (C.moveChoices Term f a) j
    simp only [moveChoices, cast_cast]
    rfl

instance (M : MapRep N) [∀ R, Fintype (Term R)] : Fintype ((C.family Term).Label M) :=
  inferInstanceAs (Fintype (∀ j, Term (C.checked M j)))

/-- The transported choice is the same term at the corresponding occurrence. -/
theorem family_move_apply (f : A.map.Iso B.map) (a : (C.family Term).Label A) (j : C.Occ A) :
    HEq ((C.family Term).move f a (C.occEquiv f j)) (a j) :=
  cast_heq _ _

/-- The checked record and its chosen term are preserved as a dependent pair. -/
theorem family_move_sigma (f : A.map.Iso B.map) (a : (C.family Term).Label A) (j : C.Occ A) :
    (⟨C.checked B (C.occEquiv f j), (C.family Term).move f a (C.occEquiv f j)⟩ : Σ R, Term R) =
      ⟨C.checked A j, a j⟩ :=
  Sigma.ext (C.checked_iso f j).symm (C.family_move_apply Term f a j)

end PortGraph.ReplacementChoices.System

end

end SpectralBooks
end LinearAlgebra
end OAI
