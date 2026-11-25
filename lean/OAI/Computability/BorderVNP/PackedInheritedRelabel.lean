import OAI.Computability.BorderVNP.PackedInheritedAddresses

/-! # Incidence addresses in an injectively named singleton cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing CellAddresses
open private endRow from OAI.Computability.BorderVNP.PackedCellAddresses
open scoped Classical

variable {D s m n : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n) (v : N.Site)

private def loops : N.InsideEdge siteID (siteID v) ≃ N.InsideEdge id v :=
  Equiv.subtypeEquivRight fun e => by simp

private def boundary : Boundary N siteID (siteID v) ≃ Boundary N id v where
  toFun e := ⟨⟨e.val.val,by simpa using e.val.property⟩,by simpa using e.property⟩
  invFun e := ⟨⟨e.val.val,by simpa using e.val.property⟩,by simpa using e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def supplied : Supplied N siteID (siteID v) ≃ Supplied N id v :=
  Equiv.sumCongr (boundary N siteID v) (Equiv.subtypeEquivRight fun p => by simp)

private theorem supplied_width (u : Supplied N siteID (siteID v)) :
    suppliedWidth N id v (supplied N siteID v u) = suppliedWidth N siteID (siteID v) u := by
  cases u <;> rfl

private theorem supplied_row (u : Supplied N siteID (siteID v)) :
    suppliedRow N id v edgeID portID (supplied N siteID v u) =
    suppliedRow N siteID (siteID v) edgeID portID u := by
  rcases u with e | p
  · by_cases hs : N.src e.val.val = v <;> simp [supplied,suppliedRow,endRow,boundary,hs]
  · rfl

private theorem sum_equiv {A B : Type*} {a : Fintype A} {b : Fintype B}
    (π : A ≃ B) (f : A → ℕ) (g : B → ℕ) (h : ∀ x, f x = g (π x)) :
    ∑ x ∈ @Finset.univ A a, f x = ∑ y ∈ @Finset.univ B b, g y :=
  @Fintype.sum_equiv _ _ ℕ a b _ π f g h

/-- Relabeling a singleton cell by its public site slot preserves its total loop width. -/
theorem guessed_relabel : guessedSize N siteID (siteID v) = guessedSize N id v := by
  unfold guessedSize
  exact sum_equiv (loops N siteID v) (fun e => N.width e.val) (fun e => N.width e.val) (fun _ => rfl)

/-- Relabeling the site preserves the total of all nonloop incident and attached words. -/
theorem supplied_relabel [Fintype P] : suppliedSize N siteID (siteID v) = suppliedSize N id v := by
  unfold suppliedSize
  exact sum_equiv (supplied N siteID v) (suppliedWidth N siteID (siteID v)) (suppliedWidth N id v)
    fun u => (supplied_width N siteID v u).symm

private theorem start_equiv {A B : Type*} {a : Fintype A} {b : Fintype B}
    (π : A ≃ B) (r : A ↪ ℕ) (t : B ↪ ℕ) (f : A → ℕ) (g : B → ℕ)
    (hr : ∀ x, t (π x) = r x) (hw : ∀ x, g (π x) = f x) (x : A) :
    @CellSlabs.start _ a r f x = @CellSlabs.start _ b t g (π x) := by
  apply @Fintype.sum_equiv _ _ ℕ a b _ π
  intro y
  simp only [hr,hw]

/-- Cable bases computed with static site-row names agree with the intrinsic site's address. -/
theorem wire_relabel [Fintype P] (z : Incident N v) :
    wireBase N siteID (siteID v) edgeID portID (fun _ => 0) ⟨v,rfl⟩ z =
    wireStart N edgeID portID v z := by
  by_cases h : N.src z.val = N.dst z.val
  · simp only [wireBase,wireStart,h,id_eq,dite_true]
    exact start_equiv (loops N siteID v) (guessedRow N siteID (siteID v) edgeID) (guessedRow N id v edgeID)
      (fun e => N.width e.val) (fun e => N.width e.val) (fun _ => rfl) (fun _ => rfl) _
  · simp only [wireBase,wireStart,Function.Embedding.apply_eq_iff_eq,h,id_eq,dite_false,externalBase,
      siteSize,Finset.sum_const_zero,Nat.add_zero,guessed_relabel]
    congr 1
    apply start_equiv (supplied N siteID v) _ _ _ _ (supplied_row N siteID edgeID portID v) (supplied_width N siteID v)

/-- Exterior port bases computed using static site rows agree with the intrinsic addresses. -/
theorem port_relabel [Fintype P] (p : Attached N v) :
    portBase N siteID (siteID v) edgeID portID (fun _ => 0) ⟨v,rfl⟩ p =
    portStart N edgeID portID v p := by
  simp only [portStart,portBase,externalBase,siteSize,Finset.sum_const_zero,Nat.add_zero,guessed_relabel]
  congr 1
  apply start_equiv (supplied N siteID v) _ _ _ _ (supplied_row N siteID edgeID portID v) (supplied_width N siteID v)

end Packing.Inherited

end BorderVNP
end Computability
end OAI
