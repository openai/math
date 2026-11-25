import OAI.Computability.IntegerMultiplication.Phase.Layout

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Tensor Net.Walsh Strip Strip.Dims Strip.Optic Packed Loom
open Finset Matrix
variable {O J R : Type} [Fintype J] [DecidableEq J] [CommRing R]
variable {P T A Bk : Tape} {h g m n : ℕ} (f : J≃Fin m) (j : J)
local notation "don" => joint P T h g J n

/-! transfer down to child Tape parameters given a Slot exhibiting station j. -/
variable (k : Slot (front P T h g n f) A (Track (chunks h g) n) Bk)
variable (e : ∀ (x : Panels P T h g J n),k.read x=x.2.1 j)
variable (u : ∀ x v,k.alter x v=(x.1,Function.update x.2.1 j v,x.2.2))
def score {P T : Tape} {h g n : ℕ} (j : J) := Strip.Optic.dig (joint P T h g J n) (gang (pier j))

def patch_r (x : Panels P T h g J n) (v : Addr (Fin n)) :=
  (x.1,Function.update x.2.1 j (fun i => pulse.symm (v i,(pulse (x.2.1 j i)).2)),x.2.2)
omit [Fintype J] in
theorem fixed_r (x : Panels P T h g J n) (v : Addr (Fin n)) :
    let a := score (P:=P) (T:=T) (h:=h) (g:=g) (n:=n) j
    a.symm (v,(a x).2) = patch_r j x v := by
  dsimp only
  have ev i z :
      (pier j).symm (v i,
        (fun u : {z:J // z≠j} => (pulse (x.2.1 u.val i)).1)) z =
      (if z=j then v i else (pulse (x.2.1 z i)).1) := by
    by_cases w : z=j <;> simp [pier,w]
  refine Prod.ext rfl (Prod.ext (funext fun a => funext fun i => ?_) rfl)
  change pulse.symm
    ((pier j).symm (v i,(fun u:{z:J // z≠j} => (pulse (x.2.1 u.val i)).1)) a,(pulse (x.2.1 a i)).2) = _
  rw [ev]
  change pulse.symm _ = Function.update x.2.1 j _ a i
  by_cases w : a=j
  · subst a; rw [ite_eq_left rfl,Function.update_self]
  rw [ite_eq_right w, Function.update_of_ne w]
  rfl

def course :=
  k.view.cast.trans (target A Bk h g (Fin n))

include u e in
omit [Fintype J] in
theorem resolve_r (x : Panels P T h g J n) (v : Addr (Fin n)) :
    let a := course f k
    a.symm (v,(a x).2) = patch_r j x v := by
  dsimp only
  rw [patch_r,← u]
  let a := k.view.cast
  change a.symm ((target A Bk h g (Fin n)).symm (v, (target A Bk h g (Fin n) (a x)).2)) = _
  rw [Slot.alter]
  congr 1
  have hz : (a x).2.1 = x.2.1 j := e _
  change ((a x).1, _,(a x).2.2) = ((a x).1, _,(a x).2.2)
  rw [← hz]
  rfl

variable (c : Quarter R)
include e u in
/-- run the child's call on the slot burst, then return, implementing exactly
a forward child operator in the distinguished column direction. -/
theorem notable (x : Panels P T h g J n → R) (b) :
    pipe don (kernel c b (lad j)) x =
    operate (target _ _ _ _ _) (allC c (fun (_ : Fin n) => b))
      (x ∘ k.view.cast.symm) ∘ k.view.cast := by
  rw [lone]
  funext y
  let a := score (P:=P) (T:=T) (h:=h) (g:=g) (n:=n) j
  let d := course f k
  let t := k.view.cast
  let m := allC c (fun (_:Fin n) => b)
  change (m *ᵥ fun i => x (a.symm (i,(a y).2))) (a y).1 =
    (m *ᵥ fun i => x (d.symm (i,(d y).2))) (d y).1
  simp_rw [show ∀ i,a.symm (i,(a y).2)=d.symm (i,(d y).2) from fun i =>
    (fixed_r j y i).trans (resolve_r f j k e u y i).symm]
  congr 1
  funext i
  change (pulse (y.2.1 j i)).1=(pulse (((k.view.cast y).2.1) i)).1
  rw [← e]
  rfl
end Phase

end IntegerMultiplication
end Computability
end OAI
