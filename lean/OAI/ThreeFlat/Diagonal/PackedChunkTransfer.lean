import OAI.ThreeFlat.Diagonal.PackedBucketBijection
import OAI.ThreeFlat.Diagonal.RotatedChunkGuards

namespace OAI
/-! # Summing a group's exact packed endpoint choices -/

namespace ThreeFlat.Diagonal.PackedChunkTransfer

open RotatedChunkGuards
open scoped BigOperators Classical

variable {n chunks a : ℕ}

def atIndex (p : Fin n → Bool) (j : ℕ) : Bool := if h : j < n then p ⟨j,h⟩ else false

abbrev Live (q : Fin chunks → Fin a → ℕ) := {i : Fin chunks × Fin a // q i.1 i.2 ≠ 0}

def project (q : Fin chunks → Fin a → ℕ) (e : Live q ≃ Fin n)
    (x : Fin chunks → Fin a → Bool) (j : Fin n) := x (e.symm j).val.1 (e.symm j).val.2

def holdsOutside (q : Fin chunks → Fin a → ℕ) (x y : Fin chunks → Fin a → Bool) :=
  ∀ i j, q i j = 0 → x i j = y i j

theorem guards_iff (q : Fin chunks → Fin a → ℕ) (e : Live q ≃ Fin n)
    (addr : ∀ z : Live q, (e z).val = q z.val.1 z.val.2-1)
    (x y : Fin chunks → Fin a → Bool) (p r : Fin n → Bool) :
    (∀ i, guard (q i) (atIndex p) (atIndex r) (x i) (y i)) ↔
      holdsOutside q x y ∧ p = project q e x ∧ r = project q e y := by
  have get (b : Fin n → Bool) (z : Live q) : atIndex b (q z.val.1 z.val.2-1) = b (e z) := by
    rw [← addr z]
    simp [atIndex,(e z).isLt]
  constructor
  · intro guards
    have kept : holdsOutside q x y := fun i j h => by simpa only [h,ite_true] using guards i j
    have atLive (z : Live q) : x z.val.1 z.val.2 = p (e z) ∧ y z.val.1 z.val.2 = r (e z) := by
      simpa only [ite_eq_right z.property,get p z,get r z] using guards z.val.1 z.val.2
    refine ⟨kept,funext (fun j => ?_),funext (fun j => ?_)⟩
    · simpa only [project,Equiv.apply_symm_apply] using (atLive (e.symm j)).1.symm
    · simpa only [project,Equiv.apply_symm_apply] using (atLive (e.symm j)).2.symm
  · rintro ⟨kept,rfl,rfl⟩ i j
    by_cases h : q i j = 0
    · simpa only [ite_eq_left h] using kept i j h
    · let z : Live q := ⟨(i,j),h⟩
      change if q z.val.1 z.val.2 = 0 then _ else _
      rw [ite_eq_right z.property,get _ z,get _ z]
      simp [project,z]

/-- Summing both proposed boundary arrays evaluates the supplied weight just
once at the selected endpoints. The formula also covers an empty group. -/
theorem sum_endpoints {F : Type*} [CommSemiring F] (q : Fin chunks → Fin a → ℕ)
    (e : Live q ≃ Fin n) (addr : ∀ z : Live q, (e z).val = q z.val.1 z.val.2-1)
    (x y : Fin chunks → Fin a → Bool) (W : (Fin n → Bool) → (Fin n → Bool) → F) :
    (∑ p, ∑ r, W p r *
      (if ∀ i, guard (q i) (atIndex p) (atIndex r) (x i) (y i) then 1 else 0)) =
      if holdsOutside q x y then W (project q e x) (project q e y) else 0 := by
  classical
  simp_rw [guards_iff q e addr x y]
  by_cases h : holdsOutside q x y
  · simp [h,mul_ite,ite_and]
  · simp [h]


end ThreeFlat.Diagonal.PackedChunkTransfer

end OAI
