import OAI.Computability.IntegerMultiplication.Phase.Room
import OAI.Computability.IntegerMultiplication.Loom.Pleat
import OAI.Computability.IntegerMultiplication.Packed.Column

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Shuttle Net.Walsh Net.Tensor Strip Strip.Dims Strip.Optic Packed Loom
open Finset Matrix
variable {J N R K I : Type} {h g n m : ℕ} {P T D S : Tape}
variable [Fintype J] [DecidableEq J]
variable [Fintype N] [DecidableEq N] [CommRing R]
-- spectral implementation on stripes indexed by fixed shape
abbrev Base (P T : Tape) (I : Type) := Pin P × I × Pin T
abbrev order (P T : Tape) (s : Series I) : Series (Base P T I) := Loom.Board P s T
abbrev Screen (h g : ℕ) (I : Type) := I → Chunk h g
abbrev plain (p b : Tape) (h g n : ℕ) := order p b (Track (chunks h g) n)

abbrev Glow (h g : ℕ) := Adic.Block 2 h × Adic.Block 2 g
def pulse : Lens (Chunk h g) Walsh.B (Glow h g) where
  toFun x := (x.1.2,(x.1.1,x.2))
  invFun x := ((x.2.1,x.1),x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

abbrev Remote (P T : Tape) h g (I : Type) := Base P T (I→Glow h g)
def target (P T : Tape) (h g) (I : Type) :
    Lens (Base P T (Screen h g I)) (Addr I) (Remote P T h g I) where
  toFun x := ((fun i => (pulse (x.2.1 i)).1),x.1,(fun i => (pulse (x.2.1 i)).2),x.2.2)
  invFun x := (x.2.1,(fun i => pulse.symm (x.1 i,x.2.2.1 i)),x.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

abbrev Panels (P T : Tape) (h g : ℕ) (J : Type) (n : ℕ) :=
  Base P T (J → Screen h g (Fin n))
abbrev front (P T : Tape) (h g n : ℕ) (f : J≃Fin m) :=
  order P T (threads (Track (chunks h g) n) f)

abbrev Lock (P T : Tape) h g (J : Type) (n : ℕ) := Base P T (J → Fin n → Glow h g)
def joint (P T : Tape) (h g : ℕ) (J : Type) (n : ℕ) :
    Optic.Layout (Panels P T h g J n) (Fin n) J (Lock P T h g J n) where
  toFun x := ((fun i j => (pulse (x.2.1 j i)).1),x.1,(fun j i => (pulse (x.2.1 j i)).2),x.2.2)
  invFun x := (x.2.1,(fun j i => pulse.symm (x.1 i j,x.2.2.1 j i)),x.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable (P T) (h g n) (f : J≃Fin m)

def bright :
    Adopt (front P T h g n f) (plain P T h g (n*m)) :=
  (Adopt.same _).split ((Loom.han (chunks h g) f n).split (Adopt.same _))
omit [Fintype J] [DecidableEq J] in
theorem lit (x) (j : J) (i : Fin n) :
    ((bright h g n P T f).cast x).2.1 (place_ f n (j,i))
      = x.2.1 j i := handled _ f _ j i

def huge (b : Type) : (J→ Fin n → b) ≃ (Fin (n*m)→b) where
  toFun v x := v ((place_ f n).symm x).1 ((place_ f n).symm x).2
  invFun u j i := u (place_ f n (j,i))
  left_inv v := by funext j i; dsimp; simp
  right_inv u := by funext i; dsimp; simp
omit [Fintype J] [DecidableEq J] in
theorem reassigned (x) :
    (bright h g n P T f).cast x = (x.1,huge n f _ x.2.1,x.2.2) := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext a
  obtain ⟨⟨j,i⟩,rfl⟩ := (place_ f n).surjective a
  rw [lit]
  dsimp only [huge,Equiv.coe_fn_mk]
  rw [Equiv.symm_apply_apply]

def corona : Batch (Fin n) J ≃ Addr (Fin (n*m)) :=
  let Z : Batch (Fin n) J ≃ (J → Fin n → B) :=
    { toFun := Function.swap, invFun := Function.swap, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  Z.trans (huge n f _)
def near : Lock P T h g J n ≃ Remote P T h g (Fin (n*m)) :=
  (Equiv.refl _).prodCongr ((huge n f _).prodCongr (Equiv.refl _))

omit [Fintype J] [DecidableEq J] in
theorem equalLayout (x) :
    target _ _ _ _ _ ((bright h g n P T f).cast x) =
      ((corona n f).prodCongr (near h g n P T f) (joint _ _ _ _ _ _ x)) := by
  rw [reassigned]; rfl

-- pullback of moving entire tensor lens
omit [DecidableEq J] in
private theorem counterpart {O V C : Type} [DecidableEq I] [Fintype I]
    (a : Mat I R) (b : Mat J R) (t : I≃J)
    (d : O≃V) (p : Lens O I C) (q : Lens V J K)
    (z : C≃K)
    (e : ∀ i, q (d i)=(t.prodCongr z) (p i))
    (ht : ∀ i j,b (t i) (t j)=a i j)
    (x : V→R) :
    operate q b x ∘ d = operate p a (x ∘ d) := by
  funext i
  have r i j : d (p.symm (i,j))=q.symm (t i,z j) := by
    apply q.injective; rw [e,Equiv.apply_symm_apply,Equiv.apply_symm_apply]; rfl
  change ∑ u, b (q (d i)).1 u * x (q.symm (u,(q (d i)).2)) =
    ∑ u, a (p i).1 u*x (d (p.symm (u,(p i).2)))
  rw [e]
  change ∑ u, b (t (p i).1) u * x (q.symm (u,z (p i).2)) = _
  let M u := b (t (p i).1) u * x (q.symm (u,z (p i).2))
  change ∑ u, M u = _
  rw [← t.sum_comp M]
  simp only [M,ht,← r]

omit [DecidableEq J] in
theorem crossing (w : Mat B R) :
    let t := Tensor.mat (fun _ : Fin (n*m) => w)
    let a := Tensor.mat (fun _ : Fin n => Tensor.mat (fun _ : J => w))
    ∀ (i j : Batch (Fin n) J), t (corona n f i) (corona n f j) = a i j := by
  dsimp only; intro x y
  simp only [Tensor.app]
  let u := ((Equiv.prodComm (Fin n) J).trans (place_ f n))
  have e (x : Batch (Fin n) J) i j : (corona n f x) (u (i,j))=x i j := by
    change (Function.swap x) ((place_ f n).symm ((place_ f n) (j,i))).1 ((place_ f n).symm ((place_ f n) (j,i))).2 = _
    rw [Equiv.symm_apply_apply]
  let c i := w (corona n f x i) (corona n f y i)
  change ∏ i,c i=_
  rw [← u.prod_comp c,Fintype.prod_prod_type]
  simp only [c,e]

theorem combination (c : Quarter R)
    (x : Base P T (Screen h g (Fin (n*m))) → R) :
    operate (target P T h g _) (allC c (fun _=>false)) x ∘ (bright _ _ n _ _ f).cast =
    pipe (joint _ _ _ _ _ _) (allC c (fun _=>false)) (x ∘ (bright h g n P T f).cast) :=
  counterpart _ _ (corona n f) _
    _ _ _ (equalLayout h g n P T f) (crossing n f _) _
end Phase

end IntegerMultiplication
end Computability
end OAI
