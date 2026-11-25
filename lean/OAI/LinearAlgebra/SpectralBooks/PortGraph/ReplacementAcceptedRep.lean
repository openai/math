import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementUniform

/-! # An accepted replacement on its finite representative -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.ReplacementTemplate.LocalRules
open UniformDecorations
variable {J I B V E : Type} {T : J → ReplacementTemplate.{0,0,0}} (R : LocalRules (I := I) T)
    {s h N : ℕ} (code : RoleLabel T ↪ Bits h) [CommSemiring B]
    (coefficient : (a : RoleLabel T) → (RolePort T a → Bits s) → B)
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (M : RootedMap V E) (cap : Fintype.card V ≤ N) (hs : M.Spherical)
    (z : V → RoleLabel T) (hz : R.Accepts M z)

/-- Give the vertices and edges of the accepted replacement consecutive
integer names, carrying its uniquely determined role assignment along. -/
def acceptedRep : (R.acceptedFamily code coefficient N).Rep :=
  let f := M.toRepIso cap hs
  ⟨M.toRep cap hs, z ∘ f.vertex.symm,
    (R.accepts_iso code M coefficient f z _ (fun v => congrArg z (f.vertex.symm_apply_apply v))).mp hz⟩

@[simp] theorem acceptedRep_role (v : V) :
    (R.acceptedRep code coefficient M cap hs z hz).2.val ((M.toRepIso cap hs).vertex v) = z v :=
  congrArg z ((M.toRepIso cap hs).vertex.symm_apply_apply v)

theorem acceptedRep_weight :
    R.acceptedWeight code coefficient ((R.acceptedFamily code coefficient N).classOf
      (R.acceptedRep code coefficient M cap hs z hz)) = R.roleContraction M coefficient ⟨z,hz⟩ := by
  let f := M.toRepIso cap hs
  let a := R.acceptedRep code coefficient M cap hs z hz
  change R.roleContraction a.1.map coefficient a.2 = _
  refine (R.decoratedContraction_role code a.1.map coefficient a.2).symm.trans ?_
  refine Eq.trans ?_ (R.decoratedContraction_role code M coefficient ⟨z,hz⟩)
  symm
  apply (R.spec code coefficient).decoratedContraction_iso f
  exact fun v => congrArg code (R.acceptedRep_role code coefficient M cap hs z hz v)

/-- Replacing the finite presentation of an accepted labelled map gives the
same class. -/
theorem acceptedRep_iso {W D : Type} [Fintype W] [Fintype D] [DecidableEq W] [DecidableEq D]
    (H : RootedMap W D) (capH : Fintype.card W ≤ N) (sH : H.Spherical)
    (y : W → RoleLabel T) (hy : R.Accepts H y)
    (f : M.Iso H) (h : ∀ v, y (f.vertex v) = z v) :
    (R.acceptedFamily code coefficient N).IsIso (R.acceptedRep code coefficient M cap hs z hz)
      (R.acceptedRep code coefficient H capH sH y hy) := by
  let fM := M.toRepIso cap hs
  let fH := H.toRepIso capH sH
  let iso := (fM.symm.trans f).trans fH
  refine ⟨iso, Subtype.ext ?_⟩
  funext v
  obtain ⟨v,rfl⟩ := iso.vertex.surjective v
  change (z ∘ fM.vertex.symm) (iso.vertex.symm (iso.vertex v)) = (y ∘ fH.vertex.symm) (iso.vertex v)
  rw [iso.vertex.symm_apply_apply]
  change z (fM.vertex.symm v) = y (fH.vertex.symm (fH.vertex (f.vertex (fM.vertex.symm v))))
  rw [fH.vertex.symm_apply_apply, h]

end PortGraph.ReplacementTemplate.LocalRules

end

end SpectralBooks
end LinearAlgebra
end OAI
