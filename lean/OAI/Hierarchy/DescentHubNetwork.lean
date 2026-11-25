import OAI.Hierarchy.DescentInitialHost

namespace OAI
/-! # The normalized hub and tether construction as an actual network -/

namespace Hierarchy.DescentInitialHost
open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _ => 1))

def hubbed : Network D P (fun _ => 1) where
  Site := Site N
  Edge := Wire N
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := source N
  dst := target N
  width := Sum.elim N.width (fun _ => 1)
  attach := Sum.inr
  position := Sum.elim N.position (fun p => N.position (N.attach p))
  in_ball := by rintro (v|p); exact N.in_ball v; exact N.in_ball (N.attach p)

def hubAssignment :
    ((p : P) → Fin 1 → Bool) × N.Assignment ≃ (hubbed N).Assignment where
  toFun a e := match e with
    | .inl t => a.2 t
    | .inr p => a.1 p
  invFun a := (fun p => a (.inr p),fun t => a (.inl t))
  left_inv _ := rfl
  right_inv a := by funext e; cases e <;> rfl

def hubTables {F : Type*} [CommSemiring F] (T : N.Tables F) : (hubbed N).Tables F
  | .inl v,z,_ => T v
      (fun ⟨e,incident⟩ => z ⟨.inl e,incident.imp (congrArg Sum.inl) (congrArg Sum.inl)⟩)
      (fun ⟨p,attached⟩ => z ⟨.inr p,Or.inl (congrArg Sum.inl attached)⟩)
  | .inr p,z,x => if z ⟨.inr p,Or.inr rfl⟩=x ⟨p,rfl⟩ then 1 else 0

theorem hub_value {F : Type*} [CommSemiring F] (T : N.Tables F) (x : Ports (fun _ : P => 1)) :
    (hubbed N).value (hubTables N T) x=N.value T x := by
  rw [←with_hubs N T x]
  unfold Network.value
  rw [←(hubAssignment N).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  let row : N.Site ⊕ P → F := fun v=>(hubbed N).read (hubTables N T) (hubAssignment N (y,a)) x v
  change (∏ v,row v)=_
  rw [Fintype.prod_sum_type row]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    change T v _ _=T v _ _
    congr 1
  · apply Finset.prod_congr rfl
    intro p _
    by_cases h : y p=x p
    · simp [row,Network.read,hubTables,hubAssignment,h]
      exact fun no=>(no rfl).elim
    · simp [row,Network.read,hubTables,hubAssignment,h]
      exact fun yes=>(h yes).elim

theorem hub_unit (tri : N.Trivalent) (e : (hubbed N).Edge) : (hubbed N).width e=1 := by
  rcases e with e|p
  · exact tri.1 e
  · rfl

theorem hub_volume : (hubbed N).bitVolume=N.bitVolume+2*Fintype.card P := by
  change Fintype.card (Site N)+Fintype.card (Wire N)+Fintype.card P=_
  rw [host_card];omega

end
end Hierarchy.DescentInitialHost

end OAI
