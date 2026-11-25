import OAI.Computability.IntegerMultiplication.Code.Loop
-- imports for chamber duplication; perhaps factor later
import OAI.Computability.IntegerMultiplication.Packed.Mixture

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
variable {A S T X Y : Type} [Codec T] [Codec X] [Codec Y]

theorem size_bel {l : List X} {x : X} (h : x ∈ l) : size x < size l := by
  induction l with
  | nil=>contradiction
  | cons a l ih=>
    simp only [size_cons]
    rcases List.mem_cons.mp h with e|e
    · subst a; omega
    specialize ih e
    omega
theorem duration (l : List X) : l.length < size l := by have := costSum_le_length_size l; omega

@[fun_prop] theorem Poly.maps (f : X→Y) (h : Poly f) : Poly (List.map f) := by
  obtain ⟨a,⟨k,C,H⟩,T⟩ := h
  let K := fun p : ℕ=> C*(p+1)^k
  have d (l : List X) : costSum a l ≤ l.length*K (size l) := by
    suffices e : ∀ (w : List X), (∀ x∈w, a x ≤ K (size l)) →
        costSum a w ≤ w.length*K (size l) by
      apply e
      intro x h
      refine (H x).trans ?_
      unfold K; gcongr; exact (size_bel h).le
    intro w
    induction w with
    | nil=> simp
    | cons b w ih=>
      intro q
      have i := ih fun x h=> q x (by simp [h])
      have t := q b (by simp)
      simp [Nat.add_mul]; omega
  apply Poly.of_bound (p:=fun x => _) (Computes.mapping T)
  apply ((Dom.base _).add ((Dom.base _).mul ((Dom.const _ C).mul (((Dom.base _).add (Dom.const _ 1)).pow k)))).mono
  intro i
  exact Nat.add_le_add_left ((d _).trans (Nat.mul_le_mul_right _ (duration i).le)) _

section Map
-- Poly closure for mapping with common data
def polyPush (f : A × S→T) (p : A×List S) := p.2.map (fun y=> f (p.1,y))
variable [Codec A] [Codec S]
private theorem dup_src (_x : S×A) : Poly (fun g:S×List A=> (g.2.map (fun _=>g.1),g.2)) := by
  have d :
      Poly (fun g : S×List A => (ruler g.2).map (fun _=> g.1)) :=
    ((Easy.pair (by fun_prop) Easy.fst).poly).compose Packed.chamber
  simp only [ruler,List.map_map] at d
  exact d.pair Easy.snd.poly
@[fun_prop] theorem Poly.push (a : A) (b : S) {f : A × S→T} (h : Poly f) :
    Poly (polyPush f) := by
  have d := (dup_src (a,b)).compose (easy_lock id Easy.identity a b).poly |>.compose (Poly.maps f h)
  have q (p : A) (t : List S) :
      lock id a b (t.map (fun _=>p),t)=t.map (fun x=> (p,x)) := by
    have e := IntegerMultiplication.Code.fair (fun _=>p) id t a b
    simp only [List.map_id] at e
    unfold lock
    rw [e,List.map_id]
    rfl
  unfold polyPush
  simpa only [q,List.map_map,Function.comp_def] using d

@[fun_prop] theorem Poly.filter (p : T→Bool) (h : Poly p) : Poly (List.filter p) := by
  have a : Poly (fun t:T=>bif p t then [t] else []) := by fun_prop
  have H := (Poly.maps _ a).compose Easy.flatten.poly
  suffices e : (List.filter p)=(fun t : List T=> (t.map (fun t=>bif p t then [t] else [])).flatten) from e ▸ H
  funext t
  induction t with
  | nil=>rfl
  | cons x t ih=> cases e : p x <;> simp_all
end Map

-- loop over tally, input width grows by fixed additive amount per turn; and stable version.
variable [Codec S]
def ride (f : S→S) (v : Tally×S) :=
  v.1.foldl (fun x _=>f x) v.2
omit [Codec S] in
theorem ride_t (f : S→S) (l:Tally) (x:S) :
    ride f (l,x)=f^[l.length] x := by
  induction l generalizing x with
  | nil=> rfl
  | cons a t ih=>
    change ride f (t,f x)=_
    simp only [List.length_cons,Function.iterate_succ_apply, ih]

-- additive bound allows iteration
@[fun_prop] theorem Poly.rider (f : S→S) (q:Poly f) (C:ℕ) (d : ∀ i,size (f i)≤ size i+C) :
    Poly (ride f) := by
  apply Poly.fold_left (f:=fun i:S×Unit=> f i.1) (by fun_prop) (C+1) 1
  have z (l:Tally) (x:S) : size (ride f (l,x)) ≤ size x+l.length*C := by
    induction l generalizing x with
    | nil=> simp; rfl
    | cons a l ih=>
      have := ih (f x)
      change size (ride f (l,f x))≤_
      rw [List.length_cons,Nat.add_mul,Nat.one_mul]
      specialize d x; omega
  rintro ⟨l,s⟩ a h
  have hs : a.length ≤ l.length := List.IsPrefix.length_le h
  rw [size_prod,size_tally,Nat.add_mul,pow_one]
  exact (z a s).trans (by nlinarith)
-- more general guards: throughout fold in fixed data, state updated with memory q preserving q. width r bound relative to orig
@[fun_prop] theorem Poly.bounder (f : S × X→X) (q : Poly f) (C:ℕ)
    (d : ∀ (x:S) (y:X),size (f (x,y)) ≤ C * size x + size y) :
    Poly (fun i : Tally × (S×X) => ((f ⟨i.2.1,·⟩)^[i.1.length]) i.2.2) := by
  let F := fun i : (S × X) × Unit => (i.1.1,f i.1)
  have hp : Poly F := by unfold F; fun_prop
  have y (x:S) (j : Tally) (b : X) :
      j.foldl (fun v k=> F (v,k)) (x,b) = (x,(fun b=> f (x,b))^[j.length] b) := by
    induction j generalizing b <;> simp [*,F,List.foldl_cons,Function.iterate_succ_apply] -- ih mentions F
  have d₂ (v : Tally × S × X) (l:Tally) (h : l <+: v.1) :
      size (l.foldl (fun i k=>F (i,k)) v.2) ≤ (2*C+2)*(size v+1)^2 := by
    rcases v with ⟨i,x,b⟩
    simp only [y,size_prod] -- fold
    have e (i : ℕ) (b : X) : size ((fun b=> f (x,b))^[i] b) ≤ size b+(C*size x)*i := by
      induction i generalizing b with
      | zero => simp
      | succ i ih =>
        rw [Function.iterate_succ_apply,Nat.mul_add]; specialize ih (f (x,b)); have := d x b; omega
    have r : l.length ≤ size i := (List.IsPrefix.length_le h).trans (duration i).le
    have t := (e l.length b).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ r) _)
    let u := size i + (size x + size b + 1) + 1
    have k : size x* size i ≤ u^2 := by unfold u; nlinarith
    unfold u at k
    have k₁ := Nat.mul_le_mul_left C k
    nlinarith
  have H := (Poly.fold_left hp _ _ d₂).sndCompose
  have y₁ (x:Tally×S×X) :
      (List.foldl (fun v k=> F (v,k)) x.2 x.1).2=(fun b=> f (x.2.1,b))^[x.1.length] x.2.2 := by
    rcases x with ⟨s,x,y'⟩; exact congrArg Prod.snd (y x s y')
  simpa only [y₁] using H

end Code

end IntegerMultiplication
end Computability
end OAI
