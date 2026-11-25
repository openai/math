import OAI.Computability.IntegerMultiplication.Brief.Signed

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- Generic polynomial time iterator for dyadic/integer table generation.
No assumption that iterating polynomial time routines is polynomial: *fixed width
at each temporary vector*. -/
namespace Garden
open Code Brief Grid Staff
abbrev Rows := List S
abbrev Brick := S × Rows
abbrev F := Rows × S
abbrev Plan := List Brick × S × Tally
-- also lock dot, truncate
abbrev Z0 : S := (false,[])
def dot (x:Rows × Rows) := Brief.wave (lock Brief.times Z0 Z0 x)
@[fun_prop] theorem dotP : Poly dot :=
  ((easy_zip Z0 Z0).poly.compose (Poly.maps _ Brief.timeP)).compose Brief.waveP

def fire (x:F × Brick) :=
  Grid.plus (Brief.times (x.2.1,x.1.2),dot (x.2.2,x.1.1))
@[fun_prop] theorem fireP : Poly fire := by unfold fire; have v:= easy_plus.poly; fun_prop
def light (x:Plan×F) : F :=
  ((polyPush fire (x.2,x.1.1)).map (fun y=>Grid.truncate0 (x.1.2.2,y)),
    Grid.truncate0 (x.1.2.2,Brief.times (x.1.2.1,x.2.2)))
@[fun_prop] theorem lamp : Poly light := by
  have H := Poly.push (([],Z0):F) ((Z0,[]):Brick) fireP
  have V := Poly.push ([]:Tally) Z0 Grid.easy_t.poly
  have t := Grid.easy_t.poly
  unfold light
  apply Poly.pair
  · change Poly (fun x : Plan×F=> polyPush Grid.truncate0 (x.1.2.2,polyPush fire (x.2,x.1.1)))
    fun_prop
  fun_prop

private theorem list_caps {A:Type} [Codec A] (l:List A) (u:ℕ) (h:∀x∈l,size x ≤ u):
    size l≤(u+1)*l.length+1 := by
  induction l with
  | nil=>simp
  | cons a b ih=>
    have t := h a (by simp)
    have v:= ih (fun x h_=> h x (by simp [h_]))
    rw [size_cons,List.length_cons]
    nlinarith

theorem lightSize (p : Plan) (v : F) :
    size (light (p,v)) ≤12*(size p+1)^2 := by
  have a : p.1.length≤ size p := (duration p.1).le.trans (by rw [size_prod (x:=p)]; omega)
  have b : p.2.2.length≤ size p := (duration p.2.2).le.trans (by rw [size_prod (x:=p),size_prod (x:=p.2)]; omega)
  unfold light
  dsimp only; rw [size_prod]
  have S (x:S): size (truncate0 (p.2.2,x)) ≤2*size p+3 := by
    rw [← Code.recover_tally p.2.2,sign_area,t_len] -- rewrites in rhs p?
    omega
  dsimp only
  let r := (polyPush fire (v,p.1)).map (fun y=>truncate0 (p.2.2,y))
  have v0 : r.length=p.1.length := by simp [r,polyPush]
  have e := list_caps r (2*size p+3) (fun y h=> by obtain ⟨i,w,rfl⟩:= List.mem_map.mp h; exact S _)
  rw [v0] at e
  change size r+size (truncate0 _)+1 ≤ _
  have B := S (times (p.2.1,v.2))
  nlinarith [Nat.mul_le_mul_left (2*size p+3+1) a]

-- Poly iteration without hypotheses when sized by control
variable {C A:Type} [Codec C] [Codec A]
theorem sole (u k:ℕ) (f : C × A→A)
    (p: Poly f) (q : ∀ c x,size (f (c,x)) ≤ u*(size c+1)^k) :
    Poly (fun t:Tally× (C × A)=>
      ((fun a=> f (t.2.1,a))^[t.1.length]) t.2.2) := by
  let F (x : (C×A)×Unit):= (x.1.1,f x.1)
  have T : Poly F := by unfold F; fun_prop
  have p0 (l:Tally) (x:C) (p:A) :
      l.foldl (fun v b=> F (v,b)) (x,p)=(x,((fun a=> f (x,a))^[l.length]) p) := by
    induction l generalizing p with
    | nil=>rfl
    | cons b l ih=>
      change List.foldl _ (x,f (x,p)) l=_
      rw [ih,List.length_cons,Function.iterate_succ_apply]
  have W := Poly.fold_left T (u+3) (k+1) (fun s l e=> by
    rcases s with ⟨t,x,a⟩
    rw [size_prod,size_prod]
    dsimp only; rw [p0,size_prod]; dsimp only
    let w := size t+(size x+size a+1)+1+1
    change _ ≤ (u+3)*w^(k+1)
    have E : w≥1 := by unfold w; omega
    have a1 : w≤w^(k+1) := Nat.le_self_pow (by omega) _
    have X : size x+size a+1≤ w := by unfold w; omega
    cases h:l.length with
    | zero=> simp only [Function.iterate_zero_apply]; nlinarith
    | succ d=>
      rw [Function.iterate_succ_apply']
      let b := q x ((fun p:A=>f (x,p))^[d] a)
      have R : (size x+1)^k ≤ w^(k+1) := by
        gcongr
        all_goals omega
      nlinarith [Nat.mul_le_mul_left u R])
  -- reduce projections
  have e (i:Tally×C×A) :
      (List.foldl (fun v b=>F (v,b)) i.2 i.1).2 = ((fun a=> f (i.2.1,a))^[i.1.length]) i.2.2 := by cases i with | mk l v=> cases v with | mk c x => exact congrArg Prod.snd (p0 l c x)
  simpa only [e] using W.sndCompose
def orbit (x:Tally × Plan × F) : F :=
  (fun v:F=>light (x.2.1,v))^[x.1.length] x.2.2
@[fun_prop] theorem polyOrbit : Poly orbit :=
  sole 12 2 light lamp lightSize
end Garden

end IntegerMultiplication
end Computability
end OAI
