import OAI.Hierarchy.DescentPackedParentIncidence
import OAI.Hierarchy.DescentOrdinaryParentSupport

namespace OAI
/-! # The original SIMD group of each positive parent in a signed successor window -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentHostDirectory DescentColonies
open scoped Classical
noncomputable section
variable {J V F P : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (rank : (J×V)↪ℕ)

theorem Stage.rotor_group {root arrived : J×V} (j : Fin A.degree)
    (hit : Stage.rotor A rank root j=some arrived) : arrived.1=root.1 := by
  unfold Stage.rotor at hit
  split at hit
  next live =>
    cases Option.some.inj hit
    have reachable:=live.choose.property
    change _ ∈ (A.near root.2).map (liftSite root.1) at reachable
    obtain ⟨_,_,eqn⟩:=Finset.mem_map.mp reachable
    exact (congrArg Prod.fst eqn).symm
  next => contradiction

theorem Stage.location_group {root arrived : J×V} (a : Address)
    (hit : location (Stage.rotor A rank) root a=some arrived) : arrived.1=root.1 := by
  unfold location at hit
  split at hit
  next =>exact (congrArg Prod.fst (Option.some.inj hit)).symm
  next =>
    split at hit
    next =>exact Stage.rotor_group A rank _ hit
    next =>contradiction

theorem Stage.walked_group {root : J×V} {w : Walk} {x : Key (J×V)}
    (actual : walked (Stage.rotor A rank) root w x) : x.1.1=root.1 := by
  have reached:=actual.1
  change ((location (Stage.rotor A rank) root (w.1,0,0)).bind _)=some x.1 at reached
  cases hop : location (Stage.rotor A rank) root (w.1,0,0) with
  | none=>simp [hop] at reached
  | some via =>
    simp only [hop,Option.bind_some] at reached
    exact (Stage.location_group A rank w.2 reached).trans (Stage.location_group A rank _ hop)

omit [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] in
private theorem post_group (hub : (J×V)→Bool) (k g : ℕ) (x : Key (J×V)) :
    (splitKey (mergeHub hub k g x)).1=x.1.1 := by
  change (mergeHub hub k g x).1.1 = x.1.1
  unfold mergeHub
  split <;> rfl

/-- Both emitted venue walks start in the unique old group recovered by
unpacking the observed next group and block. Suppressed donors cannot occur
in a window whose post-coalescence endpoint keys differ. -/
theorem Stage.group_from_parent {J₁ : Type} {k' width g : ℕ} (digits : J≃J₁×Block k')
    (hub : (J×V)→Bool) (root : J×V) (a b : Key (J×V)) (recvd : Option (Walk×Walk))
    (absent : recvd=none→a=b)
    (issued : ∀p,recvd=some p→ParentIncidence.Actual (Stage.rotor A rank) root p a b)
    (cross : mergeHub hub width g a≠mergeHub hub width g b) (atCell : J₁×Block k')
    (incident : atCell=digits (splitKey (mergeHub hub width g a)).1 ∨
                atCell=digits (splitKey (mergeHub hub width g b)).1) :
    root.1=digits.symm atCell := by
  cases found : recvd with
  | none=>exact False.elim (cross (congrArg (mergeHub hub width g) (absent found)))
  | some p =>
    have logged:=issued p found
    rcases incident with left|right
    · rw [left,Equiv.symm_apply_apply,post_group];exact (Stage.walked_group A rank logged.src).symm
    · rw [right,Equiv.symm_apply_apply,post_group];exact (Stage.walked_group A rank logged.dst).symm

end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
