import OAI.Computability.IntegerMultiplication.Code.Pace

namespace OAI
namespace Computability
namespace IntegerMultiplication

-- unary comparisons, enumeration, index helpers
namespace Code.Iter
variable {X T Y R : Type} [Codec X] [Codec Y] [Codec T] [Codec R]

@[fun_prop] theorem leader (x:X) : Easy (fun l:List X=>l.headD x) := by
  suffices e : (fun l:List X=>l.headD x) =
    (fun l=> List.casesOn (motive:=fun _=>X) l x (fun u _=>u)) from e ▸ Easy.listCase x Easy.fst
  funext l; cases l <;> rfl
def pick (x : X) (i:List X × Tally) := (i.1.drop i.2.length).headD x
@[fun_prop] theorem facile (x:X) : Easy (pick x) :=
  (Easy.exchange.compose (easy_cut Easy.identity).sndCompose).compose (leader x)
omit [Codec X] in
theorem search (l:List X) (x : X) (n : ℕ) (h:n < l.length) :
    pick x (l,tally n) = l[n] := by
  induction l generalizing n with
  | nil=> contradiction
  | cons a l ih=>
    cases n with
    | zero=>rfl
    | succ n=>exact ih n (by simpa using h)
omit [Codec X] in
theorem entry {n : ℕ} (l:Fin n→X) (i:Fin n) (x : X) :
    pick x (List.ofFn l,tally i.val) = l i := by simp [search (List.ofFn l) _ i.val (by simp)]

theorem search_size (l:List X) (s:X) (n:Tally) :
    size (pick s (l,n)) ≤ size l + size s := by
  unfold pick
  dsimp only
  cases e : l.drop n.length with
  | nil=> simp
  | cons x t=>
    have m : x∈l := by
      rw [← List.take_append_drop n.length l,e]; simp
    have := size_bel m
    simpa only [List.headD_cons] using this.le.trans (Nat.le_add_right ..)

--- comparisons on lists by length only
def small (p : List X × List Y) : Bool := decide (p.1.length<p.2.length)
@[fun_prop] theorem small_easy : Easy (small (X:=X) (Y:=Y)) := by
  have z : Easy (fun p : List X × List Y=> cutLists (ruler p.1,p.2)) := easy_cut (by fun_prop)
  have j : Easy (fun p : List Y=> if p=[] then false else true) := by
    suffices eq : (fun p : List Y=> if p=[] then false else true)=
      (fun l=>List.casesOn (motive:=fun _=>Bool) l false (fun _ _=>true)) from eq ▸ Easy.listCase false (Easy.const _)
    funext l; cases l <;> simp
  have e := z.sndCompose.compose j
  have d (l : List Y) (n:ℕ) : (if l.drop n=[] then false else true)=(decide (n<l.length):Bool) := by
    cases t : l.drop n with
    | nil =>
      have h : l.length≤n := by have := congrArg List.length t; simp at this; omega
      simp [not_lt_of_ge h]
    | cons a b=>
      have h : n<l.length := by have := congrArg List.length t; simp at this; omega
      simp [h]
  unfold small; simpa only [cutLists,ruler_length,d] using e

@[fun_prop] theorem conn_easy : Easy (fun p : Bool × Bool=>p.1 || p.2) :=
  Easy.finite _
@[fun_prop] theorem negate : Easy (fun a:Bool=>!a) := Easy.finite _ -- Bool.not
@[fun_prop] theorem linked : Easy (fun p:List X×List Y=>decide (p.1.length=p.2.length)) := by
  have v : ∀ a b:ℕ,decide (a=b) = (!(decide (a<b) || decide (b<a))) := by
    intro a b
    by_cases s:a=b; subst b; simp
    rcases Nat.lt_or_gt_of_ne s with h|h <;> simp [s,h]
  simp_rw [v]
  change Easy (fun p:List X×List Y=>!(small p || small p.swap))
  apply Easy.compose _ negate
  exact (small_easy.pair (Easy.exchange.compose small_easy)).compose conn_easy

-- extensional enumeration, “unary range”
def lineup (t : Tally) := List.ofFn fun (i:Fin t.length)=> tally (i.val)
@[simp] theorem sizeup (t : Tally) : (lineup t).length=t.length := List.length_ofFn
@[simp] theorem lined (n) :
    lineup (tally n)=List.ofFn fun (i:Fin n)=>tally i.val := by simp [lineup]

private def act (x : (List Tally × Tally) × Unit) :=
  (x.1.1++[x.1.2], ()::x.1.2)
private theorem done (i:Tally) (a:List Tally) (n:ℕ) :
    i.foldl (fun x k=> act (x,k)) (a,tally n) =
    (a++List.ofFn (fun (j:Fin i.length)=> tally (j.val+n)), tally (i.length+n)) := by
  induction i generalizing a n with
  | nil => simp
  | cons x i ih=>
    change List.foldl _ (a++[tally n], ()::tally n) i=_
    rw [← tally_succ,ih]
    congr 1
    · simp only [List.append_assoc,List.singleton_append,List.length_cons,List.ofFn_succ,Fin.val_zero,Nat.zero_add]
      congr 4; funext; simp [Nat.add_comm,Nat.add_left_comm]
    · -- tally len
      simp [Nat.add_comm,Nat.add_left_comm]

private theorem balance (i:Tally) (a:List Tally) (b:Tally) :
    let x := i.foldl (fun x k=>act (x,k)) (a,b)
    (size x.1 ≤ size a+(size b+2*i.length+2)*i.length) ∧
    (size x.2 ≤ size b+2*i.length) := by
  induction i generalizing a b with
  | nil => simp
  | cons w i ih =>
    dsimp only
    specialize ih (a++[b]) (()::b)
    have q : size (()::b)=size b+2 := by simp [show size ()=1 from rfl]; omega
    have z := size_append_right a [b]
    simp only [q,size_cons,size_nil] at * -- simp used?
    change size ((i.foldl _ (a++[b],()::b)).1)≤_ ∧ _
    rw [List.length_cons]
    constructor
    · apply ih.1.trans
      nlinarith
    exact ih.2.trans (by omega)

@[fun_prop] theorem poly_line : Poly lineup := by
  have hp := Poly.fold_left (f:=act) (by unfold act; fun_prop)
    10 2 (by
      rintro ⟨l,v,t⟩ i e
      rw [size_prod,size_prod,size_prod]
      have q := balance i v t
      have z : i.length≤l.length := List.IsPrefix.length_le e
      dsimp only
      have := duration l
      nlinarith [q.1,q.2])
  have v := Poly.compose ((Poly.identity).pair (Poly.const (([]:List Tally),tally 0))) hp.fstCompose
  unfold lineup
  simpa only [done,List.nil_append,Nat.add_zero] using v

end Code.Iter

end IntegerMultiplication
end Computability
end OAI
