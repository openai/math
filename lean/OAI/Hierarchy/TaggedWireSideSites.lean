import OAI.Hierarchy.TaggedWireTurnBoundaries

namespace OAI
/-! # Each itinerary sign is the actual side incident to the boundary site -/

namespace Hierarchy.WireTelescope.Spine
open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical

variable {K : ℕ} {E : Type} {G : PortGraph (Fin K) E} {a b : Fin K} {es : List E}

@[simp] theorem sides_first (sp : Spine G a es b) (l r : TurnRef) (n : ℕ) :
    (sp.sides l r n 0).1=l := by cases sp <;> rfl

@[simp] theorem sides_last (sp : Spine G a es b) (l r : TurnRef) (n : ℕ) :
    (sp.sides l r n (Fin.last es.length)).2=r := by
  induction sp generalizing l n with
  | nil => rfl
  | cons e t tail ih => exact ih _ _

/-- Both appearances of the same occurrence use its very own two end sites,
also when that row has appeared at an earlier position in the route. -/
theorem adjacent (sp : Spine G a es b) (l r : TurnRef) (n : ℕ) (j : Fin es.length) :
    ∃ side : Bool,
      (sp.sides l r n j.castSucc).2=.inr (n+j.val,side) ∧
      (sp.sides l r n j.succ).1=.inr (n+j.val,!side) ∧
      sp.visit j.castSucc=G.vertex (es.get j) side ∧ sp.visit j.succ=G.vertex (es.get j) (!side) := by
  induction sp generalizing l n with
  | nil => exact Fin.elim0 j
  | @cons e t xs b tail ih =>
    induction j using Fin.cases with
    | zero =>
      refine ⟨t,rfl,?_,rfl,?_⟩
      · exact sides_first tail (.inr (n,!t)) r (n+1)
      · exact visit_zero tail
    | succ j =>
      obtain ⟨s,out,arrival,leave,land⟩ := ih (.inr (n,!t)) (n+1) j
      have pos : n+1+j.val=n+j.succ.val := by change n+1+j.val=n+(j.val+1);omega
      exact ⟨s,pos ▸ out,pos ▸ arrival,leave,land⟩

theorem signed_out (sp : Spine G a es b) (diff : ∀e,G.tail e≠G.head e) (l r : TurnRef)
    (n : ℕ) (j : Fin es.length) :
    (sp.sides l r n j.castSucc).2 =
      .inr (n+j.val,decide (G.tail (es.get j) ≠ sp.visit j.castSucc)) := by
  obtain ⟨s,out,_,leave,_⟩ := adjacent sp l r n j
  rw [out,leave]
  cases s <;> simp [PortGraph.vertex,diff]

theorem signed_in (sp : Spine G a es b) (diff : ∀e,G.tail e≠G.head e) (l r : TurnRef)
    (n : ℕ) (j : Fin es.length) :
    (sp.sides l r n j.succ).1 =
      .inr (n+j.val,decide (G.tail (es.get j) ≠ sp.visit j.succ)) := by
  obtain ⟨s,_,arrival,_,land⟩ := adjacent sp l r n j
  rw [arrival,land]
  cases s <;> simp [PortGraph.vertex,diff]

/-- The native emitter may have printed either endpoint of this row first.
Testing its printed tail recovers the incident port in both orientations. -/
theorem choose_role {e : E} (diff : G.tail e≠G.head e) (tail side : Bool)
    {V : Type*} (role : Bool→V) :
    (if G.vertex e tail=G.vertex e side then role tail else role (!tail))=role side := by
  cases tail <;> cases side <;> simp [PortGraph.vertex,diff,diff.symm]

end Hierarchy.WireTelescope.Spine

end OAI
