import OAI.Computability.IntegerMultiplication.Carry.Small

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Carry
open Bits Code
/- Poly fold with common data. Allows additive C*(size control + size each input), startup arbitrary
rather than restricting fold seed, convenient. -/
variable {A X Y:Type} [Codec A] [Codec X] [Codec Y]
def trek (f : A × X × Y → X) (v : List Y × A × X) :=
  v.1.foldl (fun x y=> f (v.2.1,x,y)) v.2.2

@[fun_prop] theorem polyTrek (f : A × X × Y → X) (h:Poly f) (C:ℕ)
    (e:∀ (p:A) (x:X) (y:Y), size (f (p,x,y)) ≤ size x + C*(size p+size y)) :
    Poly (trek f) := by
  let F (i:(A × X)×Y) := (i.1.1,f (i.1.1,i.1.2,i.2))
  have H : Poly F := by unfold F; fun_prop
  have r (i:List Y) (p:A) (x:X) :
      i.foldl (fun v b=>F (v,b)) (p,x) = (p, trek f (i,p,x)) := by
    induction i generalizing x with
    | nil=>rfl
    | cons a i ih=>
      change List.foldl _ (p,f (p,x,a)) i=_
      rw [ih]; rfl
  have launch := (Poly.fold_left H (4*(C+1)) 2 (by
    rintro ⟨l,v,x⟩ a t
    dsimp only
    have w (a : List Y) (x): size (trek f (a,v,x)) ≤ size x+C*size v*a.length+C*costSum size a := by
      induction a generalizing x with
      | nil=>simp; rfl
      | cons i a ih=>
        change size (trek f (a,v,f (v,x,i))) ≤ _
        rw [List.length_cons,costSum_cons,Nat.mul_add,Nat.mul_add]
        specialize ih (f (v,x,i))
        have s := e v x i
        rw [Nat.mul_add] at s; omega
    rw [r,size_prod,size_prod,size_prod]
    obtain ⟨d,v'⟩ := t
    have W := costSum_le_length_size l
    change a++d=l at v'
    rw [← v',costSum_cat,List.length_append] at W
    rw [v'] at W
    have i := w a x
    let u:= size v+ size x+size l+5
    have q := Nat.mul_le_mul_left (C*size v) (show a.length ≤ size l by omega)
    have t := Nat.mul_le_mul_left C (show costSum size a ≤ size l by omega)
    have B := Nat.mul_le_mul_left C (show size v*size l≤ (size l+(size v+size x+1)+1+1)^2 by nlinarith)
    nlinarith [Nat.mul_le_mul_left C (show size l ≤ (size l+(size v+size x+1)+1+1)^2 by nlinarith)])).sndCompose
  have v (i:List Y×A×X): (List.foldl (fun v b=>F (v,b)) i.2 i.1).2= trek f i := by
    rcases i with ⟨l,a,x⟩; exact congrArg Prod.snd (r l a x)
  simpa only [v] using launch

-- arithmetic mixins
abbrev Two := Word × Word
@[fun_prop] theorem swift : Poly (fun i:Two=>Bits.add i) := (Bits.easy_add Easy.identity).poly
@[fun_prop] theorem minus : Poly (fun i:Two=>Bits.sub i) := (Bits.easy_sub Easy.identity).poly

def lt_ (p:Two) : Bool := (Bits.sub p).2
@[fun_prop] theorem ltPoly : Poly lt_ := minus.sndCompose
theorem lt_r (x y : Word) : lt_ (x,y)=decide (value x<value y) := by
  cases h:lt_ (x,y)
  · suffices t : ¬value x<value y by simp [t]
    intro a; have z : lt_ (x,y)=true := (sub_borrow x y).2 a; simp_all
  · simp [(sub_borrow x y).mp h]
def sub0 (p:Two) : Word :=
  bif lt_ p then [] else (Bits.sub p).1
@[fun_prop] theorem sub0_r : Poly sub0 := by unfold sub0; fun_prop
@[simp] theorem sub0_v (x y: Word) : value (sub0 (x,y))=value x-value y := by
  unfold sub0
  by_cases v:value x<value y
  · rw [lt_r,decide_eq_true v,Bool.cond_true,value_nil]; omega
  rw [lt_r,decide_eq_false v,Bool.cond_false,sub_val_le _ _ (le_of_not_gt v)]

-- schoolbook shift-add, to avoid dependency on Toom estimates
private def Xstep (p : Word×Word×Bool) :=
  Bits.add (false::p.2.1, bif p.2.2 then p.1 else [])
@[fun_prop] private theorem xCost : Poly Xstep := by unfold Xstep; fun_prop
private theorem xLen (s x:Word) (b:Bool) :
    (Xstep (s,x,b)).length ≤ x.length+s.length+2 := by
  unfold Xstep; cases b <;> simp [add_length]; omega

private theorem xSize (s x:Word) (b:Bool) :
    size (Xstep (s,x,b)) ≤ size x+3*(size s+size b) := by
  simp only [size_word,show size b=1 from rfl]
  have := xLen s x b; omega
def school (i:Two) := trek Xstep (i.2.reverse,i.1,([]:Word))

@[fun_prop] theorem polySchool : Poly school := by
  unfold school
  exact (show Easy (fun i:Two=> (i.2.reverse,i.1,([]:Word))) from by fun_prop).poly.compose
    (polyTrek _ xCost 3 xSize)

@[simp] theorem school0 (x: Word) : school (x,[])=[] := rfl
theorem school_c (x y:Word) (b:Bool) :
    school (x,b::y)=Xstep (x,school (x,y),b) := by simp [school,trek,List.foldl_append]
@[simp] theorem school_exact (x y:Word) :
    value (school (x,y))=value x*value y := by
  induction y with
  | nil=>simp
  | cons b y ih => rw [school_c]; unfold Xstep; cases b <;> simp [add_val,ih] <;> ring

-- for true needed length always resize to sum.
def times0 (x:Two) := Bits.resize (ruler (x.1++x.2),school x)
@[fun_prop] theorem polyTime : Poly times0 :=
  (((show Easy (fun x:Two=>ruler (x.1++x.2)) from by fun_prop).poly).pair polySchool).compose (easy_resize Easy.identity).poly
private theorem sizeTime (x y:Word) :
    times0 (x,y)=Bits.sized (x.length+y.length) (school (x,y)) := by
  unfold times0 sized; simp [ruler,tally]
theorem tm_length (x y:Word) :
    List.length (times0 (x,y))=x.length+y.length := by rw [sizeTime,sized_length]
theorem tm_value (x y:Word) :
    value (times0 (x,y))=value x*value y := by
  rw [sizeTime,sized_low,school_exact,pow_add]
  apply Nat.mod_eq_of_lt
  exact Nat.mul_lt_mul_of_lt_of_lt (value_lt _) (value_lt _)
end Carry

end IntegerMultiplication
end Computability
end OAI
