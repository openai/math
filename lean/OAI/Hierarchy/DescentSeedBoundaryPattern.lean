import OAI.Hierarchy.DescentSeedTrivalentMenu
import OAI.Hierarchy.DescentQuotientHistory

namespace OAI
/-! # Finite boundary patterns at the original trivalent seed sites -/
namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentInitialHost DescentPhysicalSplit
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [CommSemiring F] {D : ℕ} {P : Type} [Fintype P]
variable (N : Network D P (fun _=>1))

/-- Incidence rather than orientation indexes table arguments. A loop appears
once in this list, and the old table receives its unique word. -/
def boundaryLeg (v : N.Site) : Boundary N v ↪ Fibre N v where
  toFun x := match x with
    | .inl e=> if h : N.src e.val=v then ⟨.inr (e.val,false),by simpa [owner] using h⟩
      else ⟨.inr (e.val,true),by simpa [owner] using e.property.resolve_left h⟩
    | .inr p=>⟨.inl p.val,p.property⟩
  inj' := by
    let drop : Leg N→N.Edge⊕P := Sum.elim Sum.inr (Sum.inl ∘ Prod.fst)
    have read (x : Boundary N v) : drop ((match x with
      | .inl e=> if h : N.src e.val=v then ⟨.inr (e.val,false),by simpa [owner] using h⟩
        else ⟨.inr (e.val,true),by simpa [owner] using e.property.resolve_left h⟩
      | .inr p=>⟨.inl p.val,p.property⟩ : Fibre N v).val)=x.map Subtype.val Subtype.val := by
      cases x <;> dsimp [drop]; split <;> rfl
    intro x y h
    have eq := congrArg (fun z : Fibre N v=>drop z.val) h
    rw [read,read] at eq
    have inj : Function.Injective (fun a : Boundary N v => a.map Subtype.val Subtype.val) :=
      Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩
    exact inj eq

abbrev seedArity (v : N.Site) := Fintype.card (Boundary N v)
def boundaryIndex (v : N.Site) : Boundary N v ≃ Fin (seedArity N v) := Fintype.equivFin _

theorem seedArity_le (tri : N.Trivalent) (v : N.Site) : seedArity N v≤3 := by
  apply (Fintype.card_le_of_embedding (boundaryLeg N v)).trans
  change count N v≤3
  rw [count_eq_degree]
  exact tri.2 v

def seedPattern (single : ∀e,N.width e=1) (v : N.Site) :
    Pattern N v ≃ (Fin (seedArity N v)→Bool) where
  toFun p j := match (boundaryIndex N v).symm j with
    | .inl e=>p.1 e ⟨0,by rw [single];decide⟩
    | .inr q=>p.2 q 0
  invFun w := (fun e _=>w (boundaryIndex N v (.inl e)),fun p _=>w (boundaryIndex N v (.inr p)))
  left_inv p := by
    apply Prod.ext
    · funext e j
      simp only [Equiv.symm_apply_apply]
      apply congrArg (p.1 e)
      apply Fin.ext
      change 0=j.val
      have bound : j.val<1 := j.isLt.trans_le (single e.val).le
      omega
    · funext q j
      simp only [Equiv.symm_apply_apply]
      exact congrArg (p.2 q) (Subsingleton.elim _ _)
  right_inv f := by
    funext j
    obtain ⟨a,rfl⟩ := (boundaryIndex N v).surjective j
    cases a <;> simp only [Equiv.symm_apply_apply]


end
end Hierarchy.DescentKernelHistory

end OAI
