import OAI.Computability.BorderVNP.CubeGroupWeightSemantic
import OAI.Computability.BorderVNP.CubeSharedRowsPhysical

/-! # Group-weight words for the strict shared-record schedule

The square declaration matrix is scanned in both orders. The physical emitter
visits each increasing pair once. For a fixed group, its neighboring symbols
correspond bijectively to the emitted records incident to that group.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Physical Finset

variable {n d blocks K h : ℕ}

private def neighborRow (s : Fin d) (t : {t : Fin d // s ≠ t}) : Symbols d :=
  if h : s < t.val then ⟨(s,t.val),h⟩ else ⟨(t.val,s),lt_of_le_of_ne (le_of_not_gt h) t.property.symm⟩

private theorem neighborRow_pair (s : Fin d) (t : {t : Fin d // s ≠ t}) :
    Sym2.mk (neighborRow s t).val.1 (neighborRow s t).val.2 = Sym2.mk s t.val := by
  unfold neighborRow
  split <;> first | rfl | exact Sym2.eq_swap

/-- The square-matrix histogram reads exactly the lengths of the strict shared
records charged by the emitter, including co-located team endpoints. -/
theorem incidentWidth_eq_strict (blocks K h : ℕ) (D : LengthDeclaration n d) (s : Fin d) :
    incidentWidth blocks K h D s = SharedRows.incident blocks K h D s := by
  let width (r : Sym2 (Fin d)) := D.2 r D.1 + rowSelectorBits n d blocks K h D.1 r
  let cost (p : Symbols d) := if s = p.val.1 ∨ s = p.val.2 then SharedRows.reserved blocks K h D p else 0
  have injective : Function.Injective (neighborRow s) := by
    intro x y hxy
    apply Subtype.ext
    apply (Sym2.mkEmbedding s).injective
    exact (neighborRow_pair s x).symm.trans ((congrArg (fun p : Symbols d => Sym2.mk p.val.1 p.val.2) hxy).trans
      (neighborRow_pair s y))
  have uncovered (p : Symbols d) (miss : p ∉ Set.range (neighborRow s)) : cost p = 0 := by
    apply ite_eq_right
    rintro (hp|hp)
    · subst s
      exact miss ⟨⟨p.val.2,p.property.ne⟩,Subtype.ext (by simp [neighborRow,p.property])⟩
    · subst s
      exact miss ⟨⟨p.val.1,p.property.ne'⟩,Subtype.ext (by simp [neighborRow,p.property.not_gt])⟩
  have hit (t : {t : Fin d // s ≠ t}) : width (Sym2.mk s t.val) = cost (neighborRow s t) := by
    have belongs : s = (neighborRow s t).val.1 ∨ s = (neighborRow s t).val.2 := by
      unfold neighborRow
      split <;> simp
    simp only [cost,ite_eq_left belongs,SharedRows.reserved,neighborRow_pair,width,add_comm]
  calc
    incidentWidth blocks K h D s = ∑ t : {t : Fin d // s ≠ t}, width (Sym2.mk s t.val) := by
      rw [← sum_subtype (univ.filter fun t : Fin d => s ≠ t) (fun _ => by simp)
        (fun t => width (Sym2.mk s t)),sum_filter]
      simp only [incidentWidth,ne_eq,ite_not,width]
    _ = ∑ p, cost p := Fintype.sum_of_injective (neighborRow s) injective _ cost uncovered hit
    _ = _ := rfl

/-- The exact group words read for routing are the integer joint costs used by
the least-load pass. Both physical enumerations use the same original deliveries. -/
theorem PhysicalImage.weight_eq_groupWords {l : Layout} {mem : ℕ → ℕ} {b : ℕ}
    {D : LengthDeclaration n l.groups} {A : Type*} [Fintype A]
    {label : Fin l.cells → Label (n+1) l.groups} {recv : A → Fin l.cells} {w : A → ℕ}
    (image : PhysicalImage l mem blocks b K h D label recv w) (s : Fin l.groups) :
    l.weight mem s.val = SharedRows.groupWords (label ∘ recv) w blocks K h b D s.val := by
  rw [image.weight_eq,incidentWidth_eq_strict,SharedRows.groupWords,dite_eq_left s.isLt]
  rfl

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
