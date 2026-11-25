import Mathlib

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Curtain
open Function
variable {L : ℕ} (p : Equiv.Perm (Fin L))
def visit (x : Fin L) (k : ℕ) := (p : _ → _)^[k] x

theorem echo (x : Fin L) :
    ∃ k : ℕ, k ∈ Set.Icc 1 L ∧ visit p x k = x := by
  by_contra! h
  let v : Fin (L+1) → Fin L := fun i=> visit p x i.val
  suffices e : Function.Injective v by
    have u := Fintype.card_le_of_injective _ e
    simp at u --?
  have e : ∀ i j : Fin (L+1),i < j→ v i ≠ v j := by
    intro i j m t
    let k := j.val-i.val
    have q : j.val=i.val+k := by dsimp only [k]; exact (Nat.add_sub_of_le m.le).symm -- add_sub...?
    unfold v visit at t
    rw [q, Function.iterate_add_apply] at t
    apply h k ⟨by unfold k; exact Nat.sub_pos_of_lt m, (Nat.sub_le _ _).trans (by have := j.isLt; omega)⟩
    exact ((p.injective.iterate i.val) t).symm
  intro i j t; by_cases z : i=j
  · exact z
  rcases lt_or_gt_of_ne z with z|z
  · exact (e i j z t).elim
  exact (e j i z t.symm).elim

-- canonical orbit lists include all
def points (x:Fin L) := List.ofFn fun i:Fin L=> visit p x i.val
@[simp] theorem land (x y : Fin L) : y∈points p x ↔ ∃ k<L,visit p x k=y := by
  unfold points
  rw [List.mem_ofFn]
  exact ⟨fun ⟨i,h⟩=>⟨i,i.isLt,h⟩,fun ⟨k,e,h⟩=>⟨⟨k,e⟩,h⟩⟩
theorem center (x : Fin L) : x∈points p x :=
  (land ..).2 ⟨0,Nat.zero_lt_of_lt x.isLt,rfl⟩

theorem refuge (x:Fin L) (q:ℕ) : visit p x q ∈ points p x := by
  obtain ⟨k,⟨k0,h⟩,e⟩ := echo p x
  rw [land]; refine ⟨q % k,(Nat.mod_lt q k0).trans_le h,?_⟩
  have u : q=q%k+q/k*k := (Nat.mod_add_div' ..).symm
  have v (m n : ℕ) : visit p x (n+m*k)=visit p x n := by
    induction m with
    | zero=> simp
    | succ a ih =>
      simp only [Nat.add_mul,Nat.one_mul,← Nat.add_assoc]
      change ((p : _ → _)^[n+a*k+k]) x = _
      rw [Function.iterate_add_apply,show (p : _→_)^[k] x=x from e]
      exact ih
  rw [← v (q/k),← u]
theorem set_s (x : Fin L) :
    ∀ y,y ∈ points p x ↔ y ∈ points p (p x) := by
  intro y
  have law (n) : visit p (p x) n=visit p x (n+1) := rfl -- iterate def?
  constructor
  · intro w; obtain ⟨i,h,rfl⟩ := (land ..).1 w
    cases i with
    | zero =>
      obtain ⟨k,⟨j,i⟩,e⟩ := echo p x
      rw [land]
      change ∃ k<L, _=x
      refine ⟨k-1,by omega,?_⟩
      rw [law,show k-1+1=k by omega,e]
    | succ i => rw [← law]; exact refuge ..
  intro w; obtain ⟨i,h,rfl⟩ := (land ..).1 w
  rw [law]; exact refuge ..
theorem set_t (x : Fin L) (k : ℕ) (y) :
    y ∈ points p x ↔ y ∈ points p (visit p x k) := by
  induction k with
  | zero=> rfl
  | succ k ih =>
    rw [ih]
    change _ ↔ y ∈ points p ((p : _→_)^[k+1] x)
    rw [Function.iterate_succ_apply']
    exact set_s p _ _

-- base determined by mem and is least. define easier via Finset.min' then relate tape
def pole (x:Fin L) : Fin L :=
  (points p x).toFinset.min' (Finset.nonempty_of_ne_empty (by
    intro t
    have s : x∈(points p x).toFinset := by simp [center p x]
    rw [t] at s; contradiction))

theorem in_circle (x : Fin L) : pole p x ∈ points p x := by
  exact List.mem_toFinset.mp (Finset.min'_mem (points p x).toFinset _)
theorem first_circle (x y : Fin L) (h : y∈points p x) : pole p x≤y := by
  apply Finset.min'_le
  exact List.mem_toFinset.mpr h
theorem pole_s (x : Fin L) (q : ℕ) : pole p (visit p x q)=pole p x :=
  le_antisymm (first_circle _ _ _ ((set_t p x q _).1 (in_circle ..))) (first_circle _ _ _ ((set_t p x q _).2 (in_circle ..)))

section reflection
-- b arbitrary runtime tape-selected distance
variable (b : Fin L → ℕ) (h : ∀ x,visit p x (b x)=pole p x)
def ice (x : Fin L) : Fin L := visit p (pole p x) (b x)
def iron (x : Fin L) : Fin L := p (ice p b x)

include h
theorem glides (x : Fin L) (q : ℕ) :
    pole p (visit p (pole p x) q) = pole p x := by
  rw [pole_s]
  nth_rw 1 [← h x]; rw [pole_s]
theorem frozen (x : Fin L) :
    ice p b (ice p b x)=x := by
  let r := ice p b x
  have v := h r
  apply (p.injective.iterate (b x))
  change visit p (visit p (pole p r) (b r)) (b x)= _
  rw [← show visit p (pole p r) (b r+b x) = visit p (visit p (pole p r) (b r)) (b x) by
        simp only [visit,Nat.add_comm (b r),Function.iterate_add_apply],
      show visit p (pole p r) (b r+b x)=visit p (visit p (pole p r) (b x)) (b r) by
        simp only [visit,Function.iterate_add_apply]]
  rw [show pole p r=pole p x from glides p b h x _]
  change visit p r (b r)=visit p x (b x)
  rw [h,h]
  exact glides p b h x _
theorem shaped (x : Fin L) :
    iron p b (iron p b x)=x := by
  let n (x : Fin L):= b x+1
  let r := iron p b x
  have law (k : Fin L) : iron p b k=visit p (pole p k) (n k) := by simp [n,visit,iron,ice,Function.iterate_succ_apply']
  have fr : pole p r=pole p x := by dsimp only [r]; rw [law]; exact glides p b h x _
  have ho (x : Fin L) :
      visit p x (n x)=p (pole p x) := by
    simp [n,visit,Function.iterate_succ_apply', ← h x]
  apply p.injective.iterate (n x)
  change visit p (iron p b r) (n x)=visit p x (n x)
  rw [law,
      ← show visit p (pole p r) (n r+n x) = visit p (visit p (pole p r) (n r)) (n x) by
        simp only [visit,Nat.add_comm (n r),Function.iterate_add_apply],
      show visit p (pole p r) (n r+n x)=visit p (visit p (pole p r) (n x)) (n r) by
        simp only [visit,Function.iterate_add_apply], fr]
  rw [← law]
  change visit p r (n r) = _
  rw [ho,ho,fr]
theorem crossed (x : Fin L) : iron p b (ice p b x)=p x := by unfold iron; rw [frozen p b h]
end reflection
end Curtain

end IntegerMultiplication
end Computability
end OAI
