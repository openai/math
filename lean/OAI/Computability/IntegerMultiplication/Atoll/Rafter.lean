import OAI.Computability.IntegerMultiplication.Atoll.Order
import OAI.Computability.IntegerMultiplication.Larch.Split

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Halo Echo Param Scale Strip Cap Loom
variable {d s:ℕ}
abbrev Uni (d s:ℕ) : Bounds d:=fun _=>s
abbrev House (d s:ℕ):=Track (Series.natural s) d
-- front↔back on constant radices
private theorem monday :
    House d s=top (Uni d s):= by
  induction d with
  | zero=>
    apply sameness _ (l:=Rise (r:=Uni 0 s)) _ (best _)
    exact List.pairwise_singleton _ _
  | succ d ih=>
    change (((Series.natural s).cart _).via _) = (((Series.natural _).cart _).via _)
    change (((Series.natural s).cart (House d s)).via _) = _
    rw [ih]
    rfl
theorem tracksRuns : Runs (House d s) (Rise (r:=Uni d s)):=monday ▸ best _ -- direction
abbrev retro (d s:ℕ):Equiv.Perm (Fin d→Fin s) where
  toFun x:=fun i=>x i.rev; invFun x:=fun i=>x i.rev
  left_inv x:=by simp
  right_inv x:=by simp
abbrev Retreat (d s:ℕ):= (House d s).via (retro d s)
private theorem moon (i j: Fin d)(h:i<j): j.rev< i.rev:=Fin.rev_lt_rev.mpr h
theorem retreat_runs : Runs (Retreat d s) (Fall (r:=Uni d s)) := by
  apply transfer _ _ tracksRuns
  rintro x y ⟨i,v,h⟩
  refine ⟨i.rev,?_ ,?_⟩
  · change Digit s (x i.rev.rev) (y i.rev.rev)
    simpa using v
  intro j h'
  change x j.rev=y j.rev
  exact h j.rev (by simpa using moon i.rev j h')
theorem tuesday :
    Retreat d s=bot (Uni d s):= sameness _ retreat_runs (worst _)
-- orientation harmony
variable {n:ℕ}(h:Season n)
include h
theorem standard : Halo.walk h=top (criterion n) := by
  refine sameness (Halo.walk h) (l:=Rise) ?_ (best _)
  apply transfer _ _ (prodRuns _ _ _ (Digit _) (prodRuns _ _ (Rise (r:=Uni _ _)) (Digit _) tracksRuns (clock _)) (clock _))
  rintro ⟨⟨x,y⟩,z⟩ ⟨⟨x',y'⟩,z'⟩ q
  change Rise (gluer h (x,y,z)) (gluer h (x',y',z'))
  change ((Rise (r:=Uni _ _) x x' ∨ x=x' ∧ Digit _ y y') ∨ (x,y)=(x',y') ∧ Digit _ z z') at q
  let a:Jade n:=(x,y,z)
  let b:Jade n:=(x',y',z')
  change ∃ i:Direction n, numeral h a i<numeral h b i ∧ ∀ j:Direction n, j < i → gluer h a j=gluer h b j
  have eP (t : Scouts n) (j:x t=x' t) : gluer h a (rook t)=gluer h b (rook t):= by
    apply Fin.ext
    change numeral h a _=numeral h b _
    rw [numeralP,numeralP]; exact congrArg Fin.val j
  rcases q with (⟨i,u,m⟩|⟨e,c⟩)|⟨e,v⟩
  · have g:numeral h a (rook i)<numeral h b (rook i):= by rw [numeralP,numeralP]; exact u
    refine ⟨rook i,g,?_⟩
    intro j h
    let t:Scouts n:=⟨j.val,Nat.lt_trans h i.isLt⟩
    change gluer _ a (rook t)=gluer _ b (rook t)
    exact eP t (m t h)
  · have g : numeral h a (near h)<numeral h b (near h):=by rw [numeralS,numeralS]; exact c
    refine ⟨near h,g,fun j p=>?_⟩
    let t:Scouts n:=⟨j.val,p⟩
    change gluer _ a (rook t)=gluer _ b (rook t)
    exact eP t (congrFun e _)
  have i := Prod.mk.inj e
  have g : numeral h a (rear h)<numeral h b (rear h):=by rw [numeralR,numeralR]; exact v
  refine ⟨rear h,g,fun j p=>?_⟩
  by_cases u:j.val<Focn n
  · let t:Scouts n:=⟨j.val,u⟩
    change gluer _ a (rook t)=gluer _ b (rook t)
    exact eP t (congrFun i.1 _)
  change j.val<Focn n+1 at p
  have t:j=near h:=Fin.ext (show j.val=Focn n by omega)
  subst j
  apply Fin.ext; change numeral h a _=numeral h b _
  rw [numeralS,numeralS]; exact congrArg Fin.val i.2

omit h
abbrev Raj (n:ℕ) := dayV n × sucV n × primeV n
abbrev gus n : Jade n≃Raj n where
  toFun :=fun ⟨x,y,z⟩=>(z,y,x); invFun:=fun ⟨z,y,x⟩=>(x,y,z)
  left_inv := fun _=>rfl;right_inv:=fun _=>rfl
abbrev gold (h:Season n) : Raj n≃Tri n := (gus n).symm.trans (prism h).symm
abbrev Rim (h:Season n):Series (Tri n):=
  ((Peace n).cart ((Csys n).cart (Retreat (scouts n) (wall n)))).via (gold h)
include h
theorem rim_ : Rim h = bot (criterion n):= by
  refine sameness (Rim h) (l:=Fall) ?_ (worst _)
  apply transfer _ _ (prodRuns _ _ (Digit _) _ (clock _) (prodRuns _ _ (Digit _)
    (Fall (r:=Uni _ _)) (clock _) retreat_runs))
  rintro ⟨z,y,x⟩ ⟨z',y',x'⟩ q
  let a:Jade n:=(x,y,z)
  let b:Jade n:=(x',y',z')
  change ∃ i:Direction n,numeral h a i < numeral h b i ∧ ∀ j,i<j→ gluer h a j=gluer h b j
  change Digit _ z z' ∨ z=z' ∧ (Digit _ y y' ∨ y=y' ∧ Fall (r:=Uni _ _) x x') at q
  have sR (v:z=z'): gluer h a (rear h)=gluer h b (rear h):= by
    apply Fin.ext; change numeral h a _=numeral h b _
    rw [numeralR,numeralR]; exact congrArg Fin.val v
  have sS (v:y=y'):gluer h a (near h)=gluer h b (near h):=by
    apply Fin.ext; change numeral h a _=numeral h b _
    rw [numeralS,numeralS]; exact congrArg Fin.val v
  have sP (i:Scouts n)(v:x i=x' i):gluer h a (rook i)=gluer h b (rook i):=by
    apply Fin.ext; change numeral h a _=numeral h b _
    rw [numeralP,numeralP];exact congrArg Fin.val v
  rcases q with u|⟨v,c|⟨t,i,j,r⟩⟩
  · refine ⟨rear h,?_,cases_ h (fun i=>rear h< i→_) ?_ ?_ ?_⟩
    · rw [numeralR,numeralR]; exact u
    · intro i v; change Focn n+1< i.val at v; have M:= i.isLt; exact False.elim (by omega)
    · intro v; change Focn n+1<Focn n at v; omega
    intro v; exact (lt_irrefl _ v).elim
  · refine ⟨near h,?_,cases_ h (fun i=> near h< i→_) ?_ ?_ (fun _=>sR v)⟩
    · rw [numeralS,numeralS]; exact c
    · intro i p; change Focn n< i.val at p; exact (Nat.lt_asymm p i.isLt).elim
    intro w; exact (lt_irrefl _ w).elim
  refine ⟨rook i,?_,cases_ h (fun a₀=> rook i < a₀ → _) ?_ (fun _=>sS t) (fun _=>sR v)⟩
  · rw [numeralP,numeralP];exact j
  intro k d; exact sP k (r _ d)

end Atoll

end IntegerMultiplication
end Computability
end OAI
