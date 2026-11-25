import OAI.Computability.IntegerMultiplication.Rivulet.Pass
import OAI.Computability.IntegerMultiplication.Scale.Deeds

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Rivulet
open Param Strip IntegerMultiplication.Fourier Scale Staff Code Brief Carry

-- poly compare variable tally against all gang.
abbrev flags (x:Tally×List Tally) :=
    x.2.map (fun a=> decide (x.1.length=a.length))
@[fun_prop] theorem colors_r :
    Poly flags := by
  have Z := Poly.push ([]:Tally) ([]:Tally) (Iter.linked (X:=Unit) (Y:=Unit)).poly
  exact Z

-- count height of true
abbrev lik (x:Tally×List Tally):Tally:=
  ruler ((flags x).filter id)
@[fun_prop] theorem lik_r: Poly lik := by
  have M := (colors_r.compose (Poly.filter id Poly.identity)).compose (Easy.ruler Easy.identity).poly
  exact M
theorem priced (x: List ℕ) (i):
    lik (tally i,x.map tally) = tally (List.count i x) := by
  unfold lik flags ruler
  have H: List.map (fun a:Tally=>decide (i=a.length)) (x.map tally)=List.map (fun a=>i==a) x:= by simp [Function.comp_def,← beq_iff_eq]
  -- simple induction
  simp only [tally_length,H]
  clear H
  induction x with
  | nil=>rfl
  | cons a l ih=>
    by_cases h:i=a
    · subst a
      simp only [List.map_cons, List.filter_cons, id, beq_self_eq_true,↓reduceIte,
        List.count_cons_self]; rw [tally_succ]; exact congrArg _ ih
    simp only [List.map_cons,List.filter_cons,id,beq_iff_eq, h, Ne.symm h,↓reduceIte,List.count_cons]
    simpa [h, Ne.symm h] using ih -- maybe
variable {I:Type} {r:Regime I} (s t:I→ℕ)
variable (S:Realizes r s)(T:Realizes r t)
include S T
theorem options (g:(i:I)→Fin (t i)→ Fin (s i))
    (G:Realizes (signal t T) (fun x:Across t=>(g x.1 x.2).val)):
    r.Has (fun i=>plan (g i)) := by
  let A(i:I)(j:Fin (t i)):= tally (g i j).val
  have E:r.Has (fun i=>List.ofFn (A i)):= harvest t T A G
  apply harvest s S
  have H:= sendRoof s S (fun i=>send (List.ofFn (A i))) E
  have U := floor_ s S
  have Y:= Regime.Has.pair (r:=signal s S) (g:=fun i=>tally i.2.val) (f:=fun i=>List.ofFn (A i.1)) U H
  have k (i:I) (j:Fin (s i)):
      lik (tally j.val,List.ofFn (A i))=tally (many (g i) j) := by
    let l:= (List.ofFn (g i))
    have N: List.ofFn (A i)=((l.map Fin.val).map tally):=by unfold A l; simp only [List.map_ofFn]; rfl
    rw [N,priced]
    apply congrArg _
    change List.count _ (l.map Fin.val)=List.count _ l
    induction l with
    | nil=>rfl
    | cons a t IH=>
      by_cases h:a=j
      · subst a; simp [IH]
      · have v:a.val≠j.val:=fun e=>h (Fin.ext e)
        rw [List.map_cons,List.count_cons_of_ne v,List.count_cons_of_ne h]; exact IH
  simp_rw [← k]
  exact Y.thenDo lik_r

variable (o:I→ℤ) [∀ i,NeZero (s i)][∀ i,NeZero (t i)]
    (O:Realizes r (fun i=>(wrap (s i) (o i)).val))(h:∀i,s i≤t i)
include O
theorem shippingA :
    r.Has (fun i=>menuA (s:=s i) (t:=t i) (o i)) := by
  let f i:=river (t:=t i) (s:=s i)
  let a (i:Across t):=i.1
  have Z (p:I→ℕ)(x:Realizes r p):=landing t T p x
  have E : r.Has (fun i=>plan (f i)) := options s t S T f
    (((Z s S).times (floor_ t T)).dividing (Z t T))
  exact Regime.Has.pair (g:=fun i=>tally (s i)) S (Regime.Has.pair (g:=fun i=> tally ((wrap (s i) (o i)).val)) O E)
include h
omit [∀ (i : I), NeZero (t i)] in
theorem shippingB :
    r.Has (fun i=>menuB (h i) (o i)) := by
  let f i:=pick (s i) (t i) (h i)
  have Z (p:I→ℕ)(x:Realizes r p):=landing s S p x
  have E : r.Has (fun i=>plan (f i)):= options t s T S f
    (((((Realizes.fix 2).times (Z t T)).times (floor_ s S)).plus (Z s S)).dividing
      ((Realizes.fix 2).times (Z s S)))
  exact Regime.Has.pair (g:=fun i=>tally (s i)) S (Regime.Has.pair (g:=fun i=> tally ((wrap (s i) (o i)).val)) O E)
end Rivulet

end IntegerMultiplication
end Computability
end OAI
