import OAI.Hierarchy.ProbePayloadFabric

namespace OAI
/-! # The fixed identifications of a CT fabric form a matching on position occurrences -/

namespace Hierarchy.ProbeStage
noncomputable section

/-- Includes every intervening identification, independently of whether that position
currently holds an active record. Unlike tile links, every such identification is free. -/
def Fabric.fixedLink : {X Y : Type} → (f : Fabric X Y) → f.Column → f.Column → Prop
  | _,_,.step _ => fun _ _ => False
  | _,_,.seq a b => fun (u v : a.Column ⊕ b.Column) =>
    match u,v with
    | .inl x,.inl y => a.fixedLink x y
    | .inr x,.inr y => b.fixedLink x y
    | .inl x,.inr y => ∃ z, x=a.lastColumn z ∧ y=b.firstColumn z
    | .inr x,.inl y => ∃ z, y=a.lastColumn z ∧ x=b.firstColumn z

theorem Fabric.boundary_apart {X Y : Type} (f : Fabric X Y) (x : X) (y : Y) : f.firstColumn x ≠ f.lastColumn y := by
  cases f <;> exact Sum.inl_ne_inr

theorem Fabric.fixed_first {X Y : Type} (f : Fabric X Y) (x : X) (y : f.Column) : ¬f.fixedLink (f.firstColumn x) y := by
  induction f with
  | step s => exact id
  | seq a b ia ib =>
    cases y with
    | inl y => exact ia x y
    | inr y => exact fun ⟨z,eq,_⟩ => a.boundary_apart x z eq

theorem Fabric.fixed_last {X Y : Type} (f : Fabric X Y) (x : Y) (y : f.Column) : ¬f.fixedLink (f.lastColumn x) y := by
  induction f with
  | step s => exact id
  | seq a b ia ib =>
    cases y with
    | inr y => exact ib x y
    | inl y => exact fun ⟨z,_,eq⟩ => b.boundary_apart z x eq.symm

theorem Fabric.fixed_symm {X Y : Type} (f : Fabric X Y) (u v : f.Column) : f.fixedLink u v → f.fixedLink v u := by
  induction f with
  | step s => exact id
  | seq a b ia ib =>
    cases u <;> cases v <;> first | exact ia _ _ | exact ib _ _ | exact id

theorem Fabric.fixed_unique {X Y : Type} (f : Fabric X Y) (u v w : f.Column)
    (hv : f.fixedLink u v) (hw : f.fixedLink u w) : v=w := by
  induction f with
  | step s => contradiction
  | seq a b ia ib =>
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        cases w with
        | inl w => exact congrArg Sum.inl (ia _ _ _ hv hw)
        | inr w => obtain ⟨z,rfl,_⟩ := hw; exact False.elim (a.fixed_last z v hv)
      | inr v =>
        obtain ⟨z,rfl,rfl⟩ := hv
        cases w with
        | inl w => exact False.elim (a.fixed_last z w hw)
        | inr w => obtain ⟨z',eq,rfl⟩ := hw; rw [a.lastColumn.injective eq]
    | inr u =>
      cases v with
      | inr v =>
        cases w with
        | inr w => exact congrArg Sum.inr (ib _ _ _ hv hw)
        | inl w => obtain ⟨z,_,rfl⟩ := hw; exact False.elim (b.fixed_first z v hv)
      | inl v =>
        obtain ⟨z,rfl,rfl⟩ := hv
        cases w with
        | inr w => exact False.elim (b.fixed_first z w hw)
        | inl w => obtain ⟨z',rfl,eq⟩ := hw; rw [b.firstColumn.injective eq]

/-- Add the distinct two end banks of external tags to the same partial matching. -/
def Fabric.fixedAll {X Y : Type} (f : Fabric X Y) : f.AllColumns → f.AllColumns → Prop
  | .inl x,Sum.inr (.inl c) | .inr (.inl c),.inl x => c=f.firstColumn x
  | .inr (.inr y),.inr (.inl c) | .inr (.inl c),.inr (.inr y) => c=f.lastColumn y
  | .inr (.inl x),.inr (.inl y) => f.fixedLink x y
  | _,_ => False

theorem Fabric.all_fixed_unique {X Y : Type} (f : Fabric X Y) (u v w : f.AllColumns)
    (hv : f.fixedAll u v) (hw : f.fixedAll u w) : v=w := by
  rcases u with x|c|y
  · rcases v with a|b|d <;> rcases w with a'|b'|d' <;> simp only [fixedAll] at hv hw; try contradiction
    exact congrArg (fun z : f.Column=>Sum.inr (Sum.inl z)) (hv.trans hw.symm)
  · rcases v with a|b|d <;> rcases w with a'|b'|d' <;> simp only [fixedAll] at hv hw
    · exact congrArg Sum.inl (f.firstColumn.injective (hv.symm.trans hw))
    · rw [hv] at hw
      exact (f.fixed_first a b' hw).elim
    · exact (f.boundary_apart a d' (hv.symm.trans hw)).elim
    · rw [hw] at hv
      exact (f.fixed_first a' b hv).elim
    · exact congrArg (fun z : f.Column=>Sum.inr (Sum.inl z)) (f.fixed_unique c b b' hv hw)
    · rw [hw] at hv
      exact (f.fixed_last d' b hv).elim
    · exact (f.boundary_apart a' d (hw.symm.trans hv)).elim
    · rw [hv] at hw
      exact (f.fixed_last d b' hw).elim
    · exact congrArg (fun t : Y=>Sum.inr (Sum.inr t)) (f.lastColumn.injective (hv.symm.trans hw))
  · rcases v with a|b|d <;> rcases w with a'|b'|d' <;> simp only [fixedAll] at hv hw; try contradiction
    exact congrArg (fun z : f.Column=>Sum.inr (Sum.inl z)) (hv.trans hw.symm)

theorem Fabric.fixedAll_symm {X Y : Type} (f : Fabric X Y) (u v : f.AllColumns) : f.fixedAll u v → f.fixedAll v u := by
  rcases u with x|c|y <;> rcases v with x'|c'|y' <;> first | exact f.fixed_symm _ _ | exact id

end
end Hierarchy.ProbeStage

end OAI
