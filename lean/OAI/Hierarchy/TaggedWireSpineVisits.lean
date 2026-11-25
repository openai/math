import OAI.Hierarchy.TaggedWireStitches

namespace OAI
/-! # The site at each boundary of the actual word spine -/

noncomputable section
namespace Hierarchy.WireTelescope.Spine

open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical BigOperators

variable {S : ℕ} {E : Type} {G : PortGraph (Fin S) E} {a b : Fin S} {es : List E}

/-- Boundary zero is the starting party and boundary `j+1` is the
arrival after occurrence `j`. Both endpoints receive a turn. -/
def visit : {a b : Fin S} → {es : List E} → Spine G a es b → Fin (es.length+1) → Fin S
  | _,_,_,.nil v => fun _ => v
  | _,_,_,.cons e t tail => Fin.cases (G.vertex e t) tail.visit

@[simp] theorem visit_zero (sp : Spine G a es b) : sp.visit 0 = a := by
  cases sp <;> rfl

@[simp] theorem visit_last (sp : Spine G a es b) : sp.visit (Fin.last es.length) = b := by
  induction sp with
  | nil => rfl
  | cons e side tail ih => exact ih

/-- The sites at successive boundaries determine the word's turns even
when the physical edge row lists its two ends in the opposite order. -/
theorem visit_eq (sp : Spine G a es b) (v : Fin (es.length+1) → Fin S)
    (start : v 0 = a)
    (link : ∀ j : Fin es.length,
      (G.tail (es.get j) = v j.castSucc ∧ G.head (es.get j) = v j.succ) ∨
      (G.head (es.get j) = v j.castSucc ∧ G.tail (es.get j) = v j.succ)) :
    sp.visit = v := by
  induction sp with
  | nil a =>
    funext j
    have small := j.isLt
    change j.val < 1 at small
    have zero : j = 0 := Fin.ext (show j.val = 0 by omega)
    subst j
    exact start.symm
  | @cons e t es b tail ih =>
    have next : v (0 : Fin (es.length+1)).succ = G.vertex e (!t) := by
      have ends := link 0
      change (G.tail e = v 0 ∧ G.head e = _) ∨ (G.head e = v 0 ∧ G.tail e = _) at ends
      rw [start] at ends
      cases t <;> rcases ends with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;>
        simp only [PortGraph.vertex,Bool.not_true,Bool.not_false] at * <;> grind
    have rest := ih (fun j => v j.succ) next (fun j => link j.succ)
    funext j
    refine Fin.cases start.symm (fun q => ?_) j
    exact congrFun rest q

end Hierarchy.WireTelescope.Spine

end
end OAI
