import OAI.Computability.IntegerMultiplication.Bureau.Alcove

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Well
open Bureau Scale Brief Strip Code Param Staff Carry
variable {I:Type}
variable (n:I→ℕ)
variable (r:Regime I)
-- contains budget for ALL fixed polys in r.scale and facts
structure Origin : Prop extends Calendar r n where
  price : Regime.ripe (r:=r) (token n)

namespace Origin
variable {n r}
theorem cityA (h:∀i,Season (n i)) : Origin n (city n):=
  ⟨birthday h,(show Regime.ripe (r:=city n) _ from by
    obtain ⟨u,t⟩:=wealthy (n) -- wealthy
    refine ⟨Bureau.chargep n,fun i=>?_⟩
    obtain ⟨C,U⟩:= t i
    exact ⟨C,fun i=> (U i).trans (by gcongr; unfold token; dsimp; exact_mod_cast (Nat.le_mul_of_pos_right (load (n i)) (budget_p _) : load (n i) ≤ ton n i))⟩)⟩
end Origin
abbrev Mid (f:I→ℝ)(p q:I→Tree):=
  Carries (grant n f) (together r.header p) q
abbrev Mix(p q:I→Tree):=Carries (token n) (together r.header p) q

variable {n r}{p q a:I→Tree} (l:Origin n r)
include l
variable {f:I→ℝ}(v:∀ i,1≤f i)
theorem source (h:r.Small p): Carries (token n) r.header p:=h.cooked l.price
theorem held : close n r.header:= (source l (r.self)).small
theorem self (h:close n p): Mix n r p p:= Carries.dropLeft (Bureau.chargep n) (held l) h
theorem start (h:close n p)(g:r.Small q): Mix n r p q:=
  (Carries.dropRight (Bureau.chargep n) (held l) h).chain (source l g)
theorem start_ (h:close n p): Mix n r p r.header:= IntegerMultiplication.Well.start l h Regime.self
include v
omit l in
theorem launch (h:Mix n r p q):Mid n r f p q:=h.larger (allow_ n v)
omit l v
theorem pipe (h:Mid n r f p q)(g:Mid n r f q a):Mid n r f p a:=
  ((Carries.dropRight h.budget (Volume.left h.small) (Volume.right h.small)).twice h).chain g
theorem mix (h:Mix n r p q)(g:Mix n r q a):Mix n r p a:=
  ((Carries.dropRight h.budget (Volume.left h.small) (Volume.right h.small)).twice h).chain g
include l
theorem dispatchS (k:I→ℕ)(g:Figure r k)(v:∀ i,k i≤ton n i):
    Carries (token n) r.header (fun i=>send (tally (k i))) := by
  obtain ⟨x,e,w⟩:=g
  have t := IntegerMultiplication.Well.source l e
  obtain ⟨j,E⟩:= t.out
  have d:= rice.on x
  simp only [w] at d
  apply t.sequence
  refine ⟨t.budget,_,d,j+2,fun i=>?_⟩
  have U:(k i:ℝ)≤token n i:=by unfold token; exact_mod_cast v i
  specialize E i
  change (size (x i):ℝ)≤_ at E
  push_cast; linarith [t.budget i]

section sweep
-- pull arbitrary labels
variable {X:Type} (u:X→I)
omit l in
theorem fetch (h:r.Small p):(r.pull u).Small (p ∘ u) :=
  Task.BT.map h u
theorem along : Origin (n ∘ u) (r.pull u) := by
  obtain ⟨⟨h,⟨E,U,Y⟩,v⟩,w,j⟩:=l -- Guide.amount_?
  exact ⟨⟨fun x=>h _,⟨E ∘ u,fetch u U,fun x=>Y _⟩,fetch u v⟩,
    Bureau.chargep _,fun k=>by obtain ⟨C,z⟩:=j k; exact ⟨C,fun i=>z _⟩⟩

open Dial
-- extension by tick
variable (k:I→ℕ)(H:Realizes r k)
variable (T:I→Type)
abbrev PxB:= Dial.Hi k T
abbrev center (x:PxB k T):=x.1.whereNow
abbrev S0 := Dial.stepR (B:=T) k H
omit l in
theorem smooth {a:I→Tree}(u:r.Small a):
    (S0 k H T).Small (a ∘ center k T) :=
  fetch (fun v:PxB k T=> v.1) (Dial.small k (B:=T) H a u)
theorem slid : Origin (n ∘ center k T) (S0 k H T):= by
  obtain ⟨⟨h,⟨E,U,Y⟩,L⟩,w,j⟩:=l
  exact ⟨⟨fun x=>h _,⟨E ∘ _,smooth k H T U,fun x=>Y _⟩,smooth k H T L⟩,
    Bureau.chargep _,fun y=>by obtain ⟨C,z⟩:=j y; exact ⟨C,fun x=>z _⟩⟩
omit l in
theorem spot : Realizes (S0 k H T) (fun i:PxB k T=>(focus k i).val) :=
  (show Realizes (S0 k H T) (fun v=>v.1.tick) from Task.BT.map (Dial.tick_ k H) _).minused (.fix 1)

-- iterator cost via Breeze adapters
omit l in
theorem boil (h : close n p) : Alive r (fun _=>1) (ton n) p := by
  obtain ⟨C,U⟩:= h
  refine ⟨0,Carries.idles (unit_mass (fun _=> le_refl _) _) ⟨C,fun i=>(U i).trans (by unfold mass;push_cast; rw [one_mul]; gcongr;unfold token; simp)⟩⟩
include v
variable {s:I→ Tree}
omit l in
theorem mess (a: Mid n r f p q) : Breeze f r (fun _ =>1) (ton n) (together r.header p) q := by
  refine ⟨v,0,a.larger (fun i=> ?_)⟩
  unfold grant runrate mass token; push_cast; rw [one_mul]; gcongr; all_goals first |simp | linarith [v i]

theorem stackCap (a:Breeze f r (fun _=>1) (ton n) (together r.header p) q):
    Mid n r f p q:=by
  obtain ⟨_,k,t⟩:= a
  obtain ⟨C,U⟩:=l.price.2 k
  refine t.times (mint_ n v) (C+1) (by
    intro i
    unfold runrate mass grant
    specialize U i; push_cast at U ⊢; rw [one_mul]; have h:0≤f i:=by linarith [v i]
    change (token n i+_)*_≤_
    nlinarith [mul_le_mul_of_nonneg_right U h])

-- convert to Mid apply to any chosen value
variable (e : (i:I)→T i→Tree) (g:(i:I)→Fin (k i)→T i→ T i) (t:(i:I)→T i)
theorem sweep
    (c:close (n ∘ (Sigma.fst:Sigma T→I)) (fun (i:Sigma T)=> e i.1 i.2))
    (a:Mid (n ∘ center k T) (S0 k H T) (f ∘ center k T) (fun v:PxB k T=>e _ v.1.value)
      (fun v:PxB k T=> e _ (g (center k T v) (focus k v) v.1.value))):
    Mid n r (fun i=>f i*((k i:ℝ)+1)) (fun i=> e i (t i))
      (fun i=>e i (Dial.iter k g (Dial.start k ⟨i,t i⟩))):= by
  have d:= Dial.cyclone k f H e g (fun _=> (le_refl 1)) v (boil (r:=r.pull (Sigma.fst:Sigma T→I)) c)
    (L:=ton n) (M:=fun _=>1) (mess (f:=f ∘ center k T) (fun i=>v _) a)
  have Y:= d.along_cast (fun i:I=>(⟨i,t i⟩:Sigma T))
  exact stackCap l (fun i=>one_le_mul_of_one_le_of_one_le (v i) (by simp)) Y

omit l v
theorem result (i:I)(p:T i): Dial.iter k g (Dial.start k ⟨i,p⟩)=
    (List.ofFn (id:Fin (k i)→Fin (k i))).foldr (g i) p := by
  suffices hp: ∀ (x : Dial.Scope k T)(j)(E:x.tick=j),
    iter k g x=(List.ofFn (fun a:Fin j=> (⟨a.val,by have d:=x.limit; have h:=a.isLt; omega⟩:Fin (k x.whereNow)))).foldr (g _) x.value from
    hp _ _ rfl -- defeq
  intro x j E
  induction j generalizing x with
  | zero=> rw [Dial.iter]; dsimp only [advance]; rw [dite_eq_right (by omega)]; simp only [List.ofFn_zero,List.foldr_nil]
  | succ j ih=>
    let u:Hi k T:=⟨x,by omega⟩
    have v: (advance k g u).tick=j:=by unfold advance; dsimp [u]; omega
    rw [List.ofFn_succ',List.concat_eq_append,List.foldr_append, iter]
    dsimp only [advance]
    rw [dite_eq_left u.property]
    change iter k g (advance k g u) = _
    rw [ih (advance k g u) v]
    dsimp [advance,u]
    have f : x.tick-1=j:=by omega
    congr 2; try (exact Fin.ext f)
end sweep
end Well

end IntegerMultiplication
end Computability
end OAI
