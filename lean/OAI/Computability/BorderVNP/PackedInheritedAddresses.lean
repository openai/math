import OAI.Computability.BorderVNP.PackedBankInheritedRead
import OAI.Computability.BorderVNP.PackedCellAddressRead

/-! # Stable order of the incidence words staged at a retained site

Regard each site as a virtual cell with zero staging. Its one shared word
for every loop comes first. All nonloop endpoints and attached ports follow
in the existing public endpoint order. The word starts are therefore
exactly the canonical outputs of the cell address pass.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing CellAddresses
open scoped Classical

variable {D ne np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np) (v : N.Site)

/-- The total length of the virtual site's canonical incoming array. -/
noncomputable def incoming := guessedSize N id v + suppliedSize N id v

/-- An exterior port word attached to the specified fine site. -/
abbrev Attached := {u : P // N.attach u = v}

/-- Start of a cable in the virtual site's incoming array, counting each self-loop once. -/
noncomputable def wireStart (z : Incident N v) : ℕ := wireBase N id v edgeID portID (fun _ => 0) ⟨v,rfl⟩ z

/-- Start of an attached exterior port in the same virtual array. -/
noncomputable def portStart (u : Attached N v) : ℕ := portBase N id v edgeID portID (fun _ => 0) ⟨v,rfl⟩ u

/-- Each physical input lane of a fine site's own tensor table. -/
abbrev InputLane := (Σ z : Incident N v, Fin (N.width z.val)) ⊕ (Σ u : Attached N v, Fin (bits u.val))

private abbrev GroupLane := (Σ z : N.InsideEdge id v, Fin (N.width z.val)) ⊕
  (Σ u : Supplied N id v, Fin (suppliedWidth N id v u))

private noncomputable def group : InputLane N v ≃ GroupLane N v where
  toFun
    | .inr ⟨u,k⟩ => .inr ⟨.inr u,k⟩
    | .inl ⟨z,k⟩ =>
      if h : N.src z.val = N.dst z.val then
        .inl ⟨⟨z.val,by rcases z.property with h'|h' <;> simp_all⟩,k⟩
      else .inr ⟨.inl ⟨⟨z.val,h⟩,z.property⟩,k⟩
  invFun
    | .inl ⟨z,k⟩ => .inl ⟨⟨z.val,.inl z.property.1⟩,k⟩
    | .inr ⟨.inl u,k⟩ => .inl ⟨⟨u.val.val,u.property⟩,k⟩
    | .inr ⟨.inr u,k⟩ => .inr ⟨u,k⟩
  left_inv := by
    rintro (⟨z,k⟩ | ⟨u,k⟩)
    · dsimp only
      by_cases h : N.src z.val = N.dst z.val <;> simp only [h,dite_true,dite_false]
    · rfl
  right_inv := by
    rintro (⟨z,k⟩ | ⟨u,k⟩)
    · dsimp only
      have h : N.src z.val = N.dst z.val := z.property.1.trans z.property.2.symm
      simp only [h,dite_true]
    · rcases u with u | u
      · dsimp only
        have h : N.src u.val.val ≠ N.dst u.val.val := u.val.property
        simp only [h,dite_false]
      · rfl

/-- Address bijection in the canonical physical order, including zero-width rows. -/
noncomputable def sourceOrder : InputLane N v ≃ Fin (incoming N v) :=
  (group N v).trans ((Equiv.sumCongr
    (CellSlabs.ordinal (guessedRow N id v edgeID) (fun z => N.width z.val))
    (CellSlabs.ordinal (suppliedRow N id v edgeID portID) (suppliedWidth N id v))).trans finSumFinEquiv)

omit [Fintype P] in
private theorem external_zero : externalBase N id v (fun _ => 0) = guessedSize N id v := by
  simp [externalBase,siteSize]

/-- The cable address computed by the virtual-cell view is the stable ordered lane. -/
theorem wireOrdinal (z : Incident N v) (k : Fin (N.width z.val)) :
    (sourceOrder N edgeID portID v (.inl ⟨z,k⟩)).val = wireStart N edgeID portID v z+k.val := by
  by_cases h : N.src z.val = N.dst z.val
  · simp [sourceOrder,group,h,wireStart,wireBase,Equiv.trans_apply]
    rfl
  · simp [sourceOrder,group,h,wireStart,wireBase,Equiv.trans_apply,external_zero,Nat.add_assoc]
    rfl

/-- An attached port's ordinal follows the same external base used by the public lookup. -/
theorem portOrdinal (u : Attached N v) (k : Fin (bits u.val)) :
    (sourceOrder N edgeID portID v (.inr ⟨u,k⟩)).val = portStart N edgeID portID v u+k.val := by
  simp [sourceOrder,group,portStart,portBase,Equiv.trans_apply,external_zero,Nat.add_assoc]
  rfl

/-- End of every cable row, also when no lane is present to witness its fit. -/
theorem wireEnd_le (z : Incident N v) : wireStart N edgeID portID v z+N.width z.val ≤ incoming N v := by
  unfold wireStart wireBase
  split
  · exact (CellSlabs.end_le_capacity _ _ _).trans (Nat.le_add_right _ _)
  · rw [external_zero,Nat.add_assoc]
    exact Nat.add_le_add_left (CellSlabs.end_le_capacity _ _ _) _

/-- End of every attached port row, including zero-width ports. -/
theorem portEnd_le (u : Attached N v) : portStart N edgeID portID v u+bits u.val ≤ incoming N v := by
  rw [portStart,portBase,external_zero,Nat.add_assoc]
  exact Nat.add_le_add_left (CellSlabs.end_le_capacity _ _ _) _

end Packing.Inherited

end BorderVNP
end Computability
end OAI
