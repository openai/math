import OAI.Computability.IntegerMultiplication.Phase.Layout

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Strip Dims Loom Packed
variable {O A X : Type} {P G R S D : Tape} {a : Series O} {x : Series X}
variable {b : Series A}

/-- compatibility for forming the flat subaddress in a row add -/
abbrev Rig (a : Series O) (P G R S : Tape) (x : Series X) :=
  Adopt a (layouts P G R S x)
namespace Rig
variable (z : Rig a P G R S x)

def why (i : O) := peek (z.cast i)
def serve (i : O) (t : Triple X) := z.cast.symm (wipe (z.cast i) t)
@[simp] theorem set_r (i t) :
    z.cast (serve z i t) = wipe (z.cast i) t := by simp [serve]
def store_r (e : Seal b D) : Rig (b.cart a) (D++P) G R S x :=
  let h := e.split z
  (h.thenDo (Adopt.rotate (layout D) (layout P) _).back).thenDo ((Loom.unite D P).split (Adopt.same _))
def store_s (e : Seal b D) : Rig (a.cart b) P G R (S++D) x :=
  -- suffix re-assoc
  let c₀ := x.cart (layout S)
  let c₁ := (layout R).cart c₀
  let c₂ := x.cart c₁
  let c₃ := (layout G).cart c₂
  let c₄ := x.cart c₃
  let l₀ := (Adopt.rotate x (layout S) (layout D)).thenDo ((Adopt.same _).split (Loom.unite S D))
  let l₁ := (Adopt.rotate (layout R) c₀ (layout D)).thenDo ((Adopt.same _).split l₀)
  let l₂ := (Adopt.rotate x c₁ (layout D)).thenDo ((Adopt.same _).split l₁)
  let l₃ := (Adopt.rotate (layout G) c₂ (layout D)).thenDo ((Adopt.same _).split l₂)
  let l₄ := (Adopt.rotate x c₃ (layout D)).thenDo ((Adopt.same _).split l₃)
  ((z.split e).thenDo (Adopt.rotate (layout P) c₄ (layout D))).thenDo ((Adopt.same _).split l₄)
theorem fw (e : Seal b D) (i j) :
    why (store_r z e) (i,j) = why z j := rfl
theorem bw (e : Seal b D) (i j) :
    why (store_s z e) (i,j) = why z i := rfl
theorem do_f (e : Seal b D) (i j t) :
    serve (store_r z e) (i,j) t = (i,serve z j t) := by
  apply (store_r z e).cast.injective
  rw [set_r]
  have a (i j) : (store_r z e).cast (i,j) =
      (Union D P (e.cast i,(z.cast j).1),(z.cast j).2) := rfl
  rw [a,a,set_r]
theorem do_b (e : Seal b D) (i j t) :
    serve (store_s z e) (i,j) t = (serve z i t,j) := by
  apply (store_s z e).cast.injective
  rw [set_r]
  let en (i : Dome P G R S X) (j : Pin D) :=
    (i.1,i.2.1,i.2.2.1,i.2.2.2.1,i.2.2.2.2.1,i.2.2.2.2.2.1,Union S D (i.2.2.2.2.2.2,j))
  have a (i j) : (store_s z e).cast (i,j) = en (z.cast i) (e.cast j) := rfl
  rw [a,a,set_r]

@[simp] theorem carry (t : Adopt b a) i : why (t.thenDo z) i = why z (t.cast i) := rfl
@[simp] theorem shipped (t : Adopt b a) i k :
    serve (t.thenDo z) i k = t.cast.symm (serve z (t.cast i) k) := rfl
def corner (e : Axis a P x G x S) :
    Rig (x.cart a) [] P G S x :=
  ((Adopt.same _).split e.view).thenDo (Adopt.omitL _).back
theorem quick (e : Axis a P x G x S) i j :
    why (corner e) (i,j) = (i,e.pair j) := rfl
theorem allset (e : Axis a P x G x S) i j t :
    serve (corner e) (i,j) t = (t.1,e.bridge j t.2) := by rfl
end Rig
open Rig

private theorem follower {n} (v : Fin (n+1) → X) (i : Fin n)
    (b : X) :
    Loom.join (v 0,Function.update (fun k : Fin n => v k.succ) i b) =
    Function.update v i.succ b := by
  funext k; refine Fin.cases ?_ (fun k => ?_) k
  · simp [Function.update_of_ne (Ne.symm i.succ_ne_zero)]
  rw [tail_j]
  by_cases h : k=i
  · simp [h]
  simp [h,Fin.succ_inj]
def Trig (x : Series X) (d : Tape) {n}
    (i j k : Fin n) :=
  ∃ q : Rig (Track x n) (Rack d i.val) (Rack d (j.val-i.val-1))
      (Rack d (k.val-j.val-1)) (Rack d (n-k.val-1)) x,
    (∀ a,why q a=(a i,a j,a k)) ∧
    ∀ a w,serve q a w=
      Function.update (Function.update (Function.update a i w.1) j w.2.1) k w.2.2

variable {n : ℕ} (d : Tape) (l : Seal x d)
include l
private theorem proveA (i k : Fin n) (e : i<k) :
    Trig x d (0:Fin (n+1)) i.succ k.succ := by
  let a := Loom.pickTwo x d l i k e
  have b := a.pos
  have c := a.through
  have y := a.size
  have t₁ : a.middle = k.succ.val-i.succ.val-1 := by simp; omega
  have t₂ : a.after = n+1-k.succ.val-1 := by simp; omega
  have t₃ : a.before = i.succ.val-(0:Fin (n+1)).val-1 := by simp [b]
  unfold Trig
  rw [← t₁,← t₂,← t₃]
  refine ⟨(Loom.step x n).thenDo (Rig.corner a.shape),?_,?_⟩
  · intro t; change Rig.why (Rig.corner _) (t 0,_) = _
    rw [Rig.quick,a.who]
    rfl
  intro t w
  change Loom.join (Rig.serve (Rig.corner _) (t 0,fun k:Fin n => t k.succ) w) = _
  rw [allset,a.put]
  -- apply follower twice after initial
  rw [← follower,← follower]
  -- trouble rewriting RHS both, intervening tail
  congr

private theorem proveB (i j k : Fin n) (m : Trig x d i j k) :
    Trig x d i.succ j.succ k.succ := by
  obtain ⟨q,t,z⟩ := m
  have y : j.succ.val-i.succ.val-1=j.val-i.val-1 := by simp
  have u : k.succ.val-j.succ.val-1=k.val-j.val-1 := by simp
  have e : n+1-k.succ.val-1=n-k.val-1 := by simp
  unfold Trig
  rw [e,u,y]
  refine ⟨(step x n).thenDo (Rig.store_r q l),?_,?_⟩
  · intro v; change why (store_r ..) (v 0,_) = _
    rw [fw,t]
    rfl
  intro a w
  change Loom.join (serve (store_r q l) (a 0,fun k => a k.succ) w)=_
  rw [do_f,z,← follower,← follower,← follower]
  congr

theorem depth : {n : ℕ} → ∀ i j k : Fin n, i<j→j<k→Trig x d i j k
| 0,i,_,_,_,_ => i.elim0
| n+1,i,j,k,hs,ht => by
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact False.elim (lt_irrefl _ hs)
    | succ j =>
      induction k using Fin.cases with
      | zero => exact False.elim (not_lt_of_ge (Fin.zero_le _) ht)
      | succ k => exact proveA d l j k (Fin.succ_lt_succ_iff.mp ht)
  | succ i =>
    induction j using Fin.cases with
    | zero => exact False.elim (not_lt_of_ge (Fin.zero_le _) hs)
    | succ j =>
      induction k using Fin.cases with
      | zero => exact False.elim (not_lt_of_ge (Fin.zero_le _) ht)
      | succ k =>
        exact proveB d l i j k (depth _ _ _ (Fin.succ_lt_succ_iff.mp hs)
          (Fin.succ_lt_succ_iff.mp ht))
end Phase

end IntegerMultiplication
end Computability
end OAI
