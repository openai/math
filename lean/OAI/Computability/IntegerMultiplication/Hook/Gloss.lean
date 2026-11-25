import OAI.Computability.IntegerMultiplication.Hook.Tell
import OAI.Computability.IntegerMultiplication.Bits.Multiply

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Strip Loom Dims Code Iter Adic Packed Net Net.Walsh Phase Haze Axon Earth Staff Dusk Bits
variable {I : Type} {r : Regime I}
variable (p t:I→Tape) (f g j y w : I→ℕ) (h : ArrayCards r p t w)
    (F:Realizes r f) (G:Realizes r g) (J:Realizes r j) (Y:Realizes r y)

noncomputable section
-- q⊕u inner product exact then resize
def switch0 (x:Fin 2) : Bool := decide (x.val=1)
def tone (x : Raw 2) : Word :=
  x.reverse.map switch0
@[fun_prop] theorem poly_tone : Poly tone :=
  (Easy.reverse.compose (Easy.finite switch0).mapping).poly
private theorem value_s (v : Raw 2) :
    Bits.value (v.map switch0)=code v := by
  induction v with
  | nil=> rfl
  | cons a v ih=>
    have r : Bits.digit (switch0 a)=a.val := by fin_cases a <;> decide
    simp only [List.map_cons,Bits.value_cons,r,Adic.code,ih]
theorem value_tone (x : Raw 2) :
    Bits.value (tone x)=code x.reverse := value_s _

def boundary (x : Tally× Raw 2) : Word :=
  tone (cutLists (()::x.1,x.2)).2
@[fun_prop] theorem boundary_p : Poly boundary := by
  unfold boundary
  exact ((easy_cut ((show Easy (fun i : Tally × Raw 2=> ()::i.1) from by fun_prop).pair Easy.snd)).sndCompose.poly).compose poly_tone
variable {n m : ℕ}
private theorem tone_s (v : Raw 2) (n) :
    code ((v.drop n).reverse) = code v.reverse % (2^(v.length-n)) := by
  let L := v.take n; let T:= v.drop n
  have q : v.reverse=T.reverse ++ L.reverse := by rw [← List.reverse_append,List.take_append_drop]
  rw [q,cat,Nat.add_comm,show T.reverse.length=v.length-n by simp [T],Nat.mul_add_mod_self_left]
  refine (Nat.mod_eq_of_lt ?_).symm
  have e := limit (T.reverse)
  simpa [List.length_reverse,T] using e
theorem beyond_r (x:Face n) (i:Fin n) :
    Bits.value (boundary (box i.val,alpha x))=beyond x i := by
  unfold boundary cutLists
  rw [value_tone,tone_s]
  dsimp only
  have hlen : (Axon.alpha x).length = n := List.length_ofFn
  rw [show (()::box i.val).length=i.val+1 by simp [box],hlen]
  rfl

abbrev Clip := Tally × Word × Raw 2
def multiplier (x : Clip) := product (x.2.1,boundary (x.1,x.2.2))
def lightest (x : Clip) : Word :=
  bif switch0 (Iter.pick 0 (x.2.2,x.1)) then multiplier x else []
@[fun_prop] theorem poly_l : Poly lightest := by
  have n := (Easy.finite switch0).poly
  have e := (facile (0:Fin 2)).poly
  unfold lightest multiplier
  fun_prop

theorem ordinary (x : Face n) (i:Fin n) (q:Word) :
    Bits.value (lightest (box i.val,q,alpha x)) =
      Bits.value q*Axon.pin (x i)*beyond x i := by
  unfold lightest
  dsimp only
  have ePick : Iter.pick (0:Fin 2) (Axon.alpha x, box i.val) = (x i : Fin 2) :=
    Iter.entry (fun a : Fin n => (x a : Fin 2)) i (0:Fin 2)
  rw [ePick]
  have z : ∀ t : Fin 2,t=0 ∨ t=1 := by decide
  rcases z (x i) with t|t -- defeq Fin B
  · simp only [t,show switch0 0=false by decide,Bool.cond_false]
    change 0 = Bits.value q*0*_
    simp
  simp only [t,show switch0 1=true by decide,Bool.cond_true,multiplier]
  rw [Bits.exact_prod,beyond_r]
  change _=Bits.value q*1*_
  simp

def sumN (v:List Word) := v.foldl (fun a b=>Bits.add (a,b)) []
private theorem gain (v:List Word) (b : Word) :
    let Z := v.foldl (fun a b=>Bits.add (a,b)) b
    (size Z ≤ 3*size v+size b) ∧ Bits.value Z=(v.map Bits.value).sum + Bits.value b := by
  dsimp only
  induction v generalizing b with
  | nil=> simp
  | cons a v ih=>
    specialize ih (Bits.add (b,a))
    simp only [List.map_cons,List.foldl_cons,List.sum_cons,size_cons]
    rw [add_val] at ih
    have y := ih.1
    rw [size_word (add (b,a)),add_length] at y
    simp only [size_word] at y ⊢
    constructor
    · omega
    exact ih.2.trans (by omega)
@[fun_prop] theorem sumN_p : Poly sumN := by
  unfold sumN
  refine Poly.compose (g:=fun x:List Word × Word=> x.1.foldl (fun a b=>Bits.add (a,b)) x.2) ((Poly.identity).pair (Code.Poly.const (X:=List Word) ([]:Word))) ?_
  apply Poly.fold_left (f:=Bits.add) ((easy_add Easy.identity).poly) 4 1
  intro p i h
  obtain ⟨s,h⟩ := h
  have e := size_append_right i s
  have r := (gain i p.2).1
  rw [pow_one,size_prod,← h]
  omega

def wrap (x : (Tally × Tally) × (List Word × List (Raw 2))) :=
  let v := sumN (polyPush (fun (i : Tally × Word×Raw 2)=> lightest i) (x.1.1,lock id ([]:Word) ([]:Raw 2) x.2))
  Bits.resize (x.1.2,Bits.shift (x.1.1,v))
@[fun_prop] theorem polyWrap : Poly wrap := by
  have h := Poly.push ([]:Tally) (([]:Word),([]:Raw 2)) poly_l
  have q := (easy_lock id Easy.identity ([]:Word) ([]:Raw 2)).poly
  have P : Poly Bits.resize := (easy_resize Easy.identity).poly
  have Z : Poly Bits.shift := (easy_shift Easy.identity).poly
  unfold wrap; dsimp only [id_eq]
  fun_prop

abbrev θ (i : Fin n) (q:Fin m→ ℕ) (x : Scr (Fin m) n) :=
  2^i.val * ∑ v,q v * Axon.pin (x v i) * beyond (x v) i
private theorem paired_fn {v : ℕ}
    (x:Fin v→Word) (y:Fin v→ Raw 2) :
    lock id ([]:Word) ([]:Raw 2) (List.ofFn x,List.ofFn y)=
    List.ofFn (fun i => (x i,y i)) := by
  have e {A : Type} (x:Fin v→A) : (Strip.Series.natural v).tab x=List.ofFn x := by
    change List.map x (List.ofFn id)=_
    rw [List.map_ofFn]; rfl
  simp only [← @e Word,← @e (Raw 2),← @e (Word × Raw 2)]
  exact Code.paired id x y (Series.natural v) ([]:Word) ([]:Raw 2)
abbrev target_ (i : Fin n) (q : Fin m → Word) (z : Scr (Fin m) n) :=
    wrap ((box i.val,box n),List.ofFn q,List.ofFn fun i=> Axon.alpha (z i))
theorem wrap_val (i : Fin n) (q : Fin m → Word) (z : Scr (Fin m) n) :
    Bits.value (target_ i q z)= θ i (Bits.value ∘ q) z % 2^n := by
  unfold target_ wrap
  dsimp only
  change Bits.value (Bits.sized n _)=_
  rw [Bits.sized_low,shift_value, paired_fn]
  simp only [box,tally_length,sumN,Code.polyPush,List.map_ofFn]
  rw [(gain ..).2]
  simp only [Bits.value_nil,add_zero,List.map_ofFn,Function.comp_def,ordinary,List.sum_ofFn] -- ordinary expects box and eta exact?
theorem wrap_len (i : Fin n) (q : Fin m → Word) (z : Scr (Fin m) n) : (target_ i q z).length=n :=
  Bits.sized_length ..

variable (i:(a:I)→Fin (Ht (g a) (j a) (y a))) (q : (i:I)→Fin (f i)→Word)
variable (Q:r.Has (fun i=>List.ofFn (q i))) (Ih : Realizes r (fun a=> (i a).val))
abbrev focus (x:I) (a:baz (p x) (t x) (f x) (g x) (j x) (y x)) :=
  target_ (i x) (q x) (legend a.2.1)
include h F G J Y Ih Q
theorem offered :
    Strip.Trace r (zone p t f g j y) (fun x a=> send (focus p t f g j y i q x a)) := by
  have t₀ := testimony p t f g j y w h F G J Y
  let A i := baz (p i) (t i) (f i) (g i) (j i) (y i); let Z := Sigma A
  let hat (i:I) (x:A i) := terms x
  apply t₀.tune
  let S := onboard r (fun i x=> send (hat i x)) t₀.meter
  have E : S.Has fun i:Z=> hat i.1 i.2 := onboard_hat _ t₀.meter
  have sm {A} [Codec A] (v:I→A) (z:r.Has v) : S.Has (v ∘ Sigma.fst) :=
    onboard_small _ t₀.meter _ z
  exact (((sm _ Ih).pair (sm _ ((G.times J).plus Y))).pair ((sm _ Q).pair E)).thenDo polyWrap
end
end Hook

end IntegerMultiplication
end Computability
end OAI
