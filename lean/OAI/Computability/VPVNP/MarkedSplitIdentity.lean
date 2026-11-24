import OAI.Computability.VPVNP.MarkedTensor

/-!
# Splitting a marked tensor times an identity wire

In Appendix A.2 the new marked index is placed at the intermediate party. The
column of the exterior operator stays at the first endpoint and its row at
the second. These three roles retain their own local factors even when their
parties coincide.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

universe w

variable {J k : Type*}

/-- The new marked index, the exterior column, and the exterior row. -/
abbrev tripleBasis (I H : Type w) := cutBasis (fun _ : Bool ↦ H) I

/-- Place the new index at `x`, the column at `a`, and the row at `b`. -/
def triplePlace (x a b : J) : Option Bool → J
  | none => x
  | some false => a
  | some true => b

/-- Place the table indexed by the new index, row, and column, in that order. -/
noncomputable abbrev threeMarked (B : J → Type*) [∀ j, Fintype (B j)]
    (I H : Type w) [Fintype I] [Fintype H] (x a b : J)
    (S : ((j : J) → B j) → I → H → H → k) : Tensor k J :=
  placedWith B (tripleBasis I H) (triplePlace x a b)
    (fun bg y ↦ S bg (y none) (y (some true)) (y (some false)))

/-- Contract the old marked index against one of the two exterior-operator orders. -/
noncomputable abbrev splitMarkedTerm [CommSemiring k] (B : J → Type*) [∀ j, Fintype (B j)]
    (I H : Type w) [Fintype I] [Fintype H] (x a b : J)
    (T : ((j : J) → B j) → I → k) (M : I → I → H → H → k) : Tensor k J :=
  threeMarked B I H x a b (fun bg i β α ↦ ∑ j, T bg j * M i j β α)

open scoped Classical in
/-- Grouping the three indices of the marked tensor and the wire gives the
coefficient of the marked tensor times the row-column Kronecker delta. -/
theorem marked_wire_mutual [CommSemiring k] [Fintype J]
    (B : J → Type*) [∀ j, Fintype (B j)] (I H : Type w) [Fintype I] [Fintype H]
    (x a b : J) (T : ((j : J) → B j) → I → k) :
    let X := tensorProduct (marked B I x T) (wire a b H)
    let Y := threeMarked B I H x a b
      (fun bg i β α ↦ T bg i * (if α = β then 1 else 0))
    Restricts X Y ∧ Restricts Y X := by
  let e (j : J) : (B j × ((r : Option Bool) → j = triplePlace x a b r → tripleBasis I H r)) ≃
      (B j × (j = x → I)) × ((j = a → H) × (j = b → H)) :=
    { toFun z := ((z.1, z.2 none), z.2 (some false), z.2 (some true))
      invFun p := (p.1.1, fun r ↦ match r with
        | none => p.1.2
        | some false => p.2.1
        | some true => p.2.2)
      left_inv z := by
        refine Prod.ext ?_ ?_
        · rfl
        funext r
        rcases r with _ | (_ | _) <;> rfl
      right_inv _ := rfl }
  exact restricts_of_reindex e (fun _ ↦ rfl)

open scoped Classical in
/-- The two contracted arrays dominate the product of the marked tensor and
its identity wire under direct sum. -/
theorem marked_split_restricts [CommSemiring k] [Fintype J]
    (B : J → Type*) [∀ j, Fintype (B j)] (I H : Type w) [Fintype I] [Fintype H]
    (x a b : J) (T : ((j : J) → B j) → I → k) (P M : I → I → H → H → k)
    (h : ∀ i j β α, P i j β α + M i j β α = if i = j ∧ β = α then 1 else 0) :
    Restricts (directSum (splitMarkedTerm B I H x a b T P) (splitMarkedTerm B I H x a b T M))
      (tensorProduct (marked B I x T) (wire a b H)) := by
  let L := splitMarkedTerm B I H x a b T P
  let R := splitMarkedTerm B I H x a b T M
  let Y := threeMarked B I H x a b (fun bg i β α ↦ T bg i * (if α = β then 1 else 0))
  let LC : Array k L.Basis := L.coeff
  let RC : Array k L.Basis := R.coeff
  let YC : Array k L.Basis := Y.coeff
  have hsum : LC + RC = YC := by
    funext z
    let bg := fun j ↦ (z j).1
    let i : I := (z x).2 none rfl
    let α : H := (z a).2 (some false) rfl
    let β : H := (z b).2 (some true) rfl
    change (∑ j, T bg j * P i j β α) + (∑ j, T bg j * M i j β α) =
      T bg i * (if α = β then 1 else 0)
    rw [← Finset.sum_add_distrib]
    simp_rw [← mul_add, h]
    by_cases he : β = α <;> simp [he, eq_comm (a := α) (b := β)]
  refine (directSum_restricts_add LC RC).trans ?_
  rw [hsum]
  exact (marked_wire_mutual B I H x a b T).2

open scoped Classical in
/-- Applying the spectral point gives the subadditivity step of the relocation inequality. -/
theorem value_marked_wire_le_split [Field k] [Fintype J] (F : SpectralPoint k J)
    (B : J → Type) [∀ j, Fintype (B j)] (I H : Type) [Fintype I] [Fintype H]
    (x a b : J) (T : ((j : J) → B j) → I → k) (P M : I → I → H → H → k)
    (h : ∀ i j β α, P i j β α + M i j β α = if i = j ∧ β = α then 1 else 0) :
    F.value (marked B I x T) * F.value (wire a b H) ≤
      F.value (splitMarkedTerm B I H x a b T P) + F.value (splitMarkedTerm B I H x a b T M) := by
  rw [← F.value_tensorProduct, ← F.value_directSum]
  exact F.monotone (marked_split_restricts B I H x a b T P M h)

end WireTensor

end VPVNP
end Computability
end OAI
