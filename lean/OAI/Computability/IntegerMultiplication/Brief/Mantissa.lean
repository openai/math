import OAI.Computability.IntegerMultiplication.Brief.Plan
import OAI.Computability.IntegerMultiplication.Grid.Tax

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- Polynomial-sized signed integer code -/
namespace Brief
open Code Carry Grid Bits Staff Strip

def register (w:Word): S := (false,w)
theorem regV (w) :
    whole (register w)=value w := by simp [whole,register,tag]
@[fun_prop] theorem positivist : Poly register := by unfold register; fun_prop

def times (x:S×S):S := (signX (x.1.1,x.2.1), Carry.times0 (x.1.2,x.2.2))
@[fun_prop] theorem timeP : Poly times := by
  unfold times
  have T := (Easy.finite Grid.signX).poly
  fun_prop
@[simp] theorem timeV (u v:S) :
    whole (times (u,v))=whole u*whole v := by unfold times whole; rw [tm_value,Nat.cast_mul, sign_r]; ring
theorem timeS (u v : S) :
    size (times (u,v)) ≤ size u+size v := by unfold times; rw [sign_area,sign_area,sign_area]; unfold dept; rw [tm_length]; dsimp only; omega

theorem plusS (x y:S) :
    size (plus (x,y)) ≤ size x+size y := by
  simp only [Grid.plus,minusMax,takePlus,takeSub, sign_area]
  cases u:decide (x.1=y.1) <;> cases v:Grid.borrow (x,y)
  <;> simp [dept, sub_length, add_length] <;> omega

-- is x ≥ 0? quadratic
def negative (x:S): Bool :=
  x.1 && (lt_ ([],x.2))
@[fun_prop] theorem negativeP : Poly negative := by
  unfold negative
  exact Poly.compose ((Poly.identity.fstCompose).pair ((show Poly (fun x:S=> (([]:Word),x.2)) from by fun_prop).compose ltPoly)) (Easy.finite (fun x:Bool×Bool=>x.1&&x.2)).poly
theorem negated {x:S} : negative x= decide (whole x<0) := by
  unfold negative whole
  rw [lt_r]
  cases h:x.1
  · simp [tag]
  by_cases a:value x.2=0
  · simp [tag,a]
  have v : (0:ℤ) < value x.2 := by exact_mod_cast Nat.pos_of_ne_zero a
  rw [value_nil]; simp [tag, Nat.pos_of_ne_zero a]

def before (x:S×S):Bool :=
  negative (plus (x.1,Grid.neg x.2))
theorem beforeV (x y) : before (x,y) = decide (whole x < whole y) := by
  unfold before; dsimp only; rw [negated,plus_v,Grid.neg_r]
  exact decide_eq_decide.mpr (by omega)
@[fun_prop] theorem beforeP : Poly before :=
  (Easy.poly (f:=fun x:S×S=> plus (x.1,Grid.neg x.2)) (by fun_prop)).compose negativeP

abbrev sq (x:S×Word) : S :=
  (x.1.1,(nat_div (x.1.2,x.2)).1)
@[fun_prop] theorem quotientP : Poly sq := by unfold sq; fun_prop
-- Sign truncate division. establish directly norm close with x.1 representation, including x=0 negative flag
theorem sq_abs (x:S) (y:Word) :
    (whole (sq (x,y))).natAbs=value x.2/value y := by rw [normal]; exact (division_rules x.2 y).1

theorem sq_close (x:S) (y:Word) (v : 0 < value y):
    |(whole (sq (x,y)):ℝ) - (whole x:ℝ)/(value y:ℝ)| ≤ 1 := by
  have e (a b:ℕ) (v : 0<b):
      |((a/b:ℕ):ℝ) - (a:ℝ)/(b:ℝ)| ≤1 := by
    have h:(0:ℝ)<b := by exact_mod_cast v
    rw [abs_le]
    constructor
    · have E:= (((div_le_iff₀ h).mpr (show (a:ℝ)≤(1+(a/b:ℕ))*b from by
        exact_mod_cast (show a≤(1+a/b)*b by
          have z:= Nat.div_add_mod' a b
          have y:= Nat.mod_lt a v
          rw [Nat.add_mul,Nat.one_mul]; omega)))
        : (a:ℝ)/b ≤ 1+(a/b:ℕ))
      linarith
    · have g : ((a/b:ℕ):ℝ) ≤ (a:ℝ)/b :=
        (le_div_iff₀ h).mpr (by exact_mod_cast Nat.div_mul_le_self _ _)
      linarith
  unfold whole
  rw [Int.cast_mul,Int.cast_mul, ← mul_div_assoc', ← mul_sub,abs_mul]
  have h : |((tag x.1:ℤ):ℝ)|=1 := by exact_mod_cast Grid.tag_v x.1
  rw [h,one_mul]
  simp only [Int.cast_natCast,(division_rules x.2 y).1]
  exact e _ _ v

-- list sum and product
def wave (x:List S): S := trek (fun i:Unit×S×S=> Grid.plus i.2) (x,(),false,[])
def chains (x:List S) : S := trek (fun i:Unit×S×S=>times i.2) (x,(),false,[true])
@[fun_prop] theorem waveP : Poly wave := by
  unfold wave
  exact Poly.compose (show Poly (fun i:List S=> (i,(),false,([]:Word))) from by fun_prop)
    (polyTrek _ ((Easy.snd.compose easy_plus).poly) 1 (by intro _ x y; dsimp only; have h:=plusS x y; omega))
@[fun_prop] theorem chainsP : Poly chains := by
  unfold chains
  exact Poly.compose (show Poly (fun i:List S=> (i,(),false,([true]:Word))) from by fun_prop)
    (polyTrek _ (by fun_prop) 1 (by intro _ x y; have h:=timeS x y; dsimp only; omega))
theorem waveV (x:List S):
    whole (wave x)=(x.map whole).sum := by
  have e (p:S) (q:List S) :
    whole (q.foldl (fun x b=>Grid.plus (x,b)) p)= whole p+(q.map whole).sum := by
    induction q generalizing p with
    | nil=>simp
    | cons a q ih=>
      simp only [List.foldl_cons,ih,plus_v,List.map_cons,List.sum_cons]; ring
  change whole (List.foldl (fun x b=>plus (x,b)) (false,[]) x)=_
  rw [e,show whole (false,[])=0 from rfl,zero_add]
theorem chainsV (x:List S):
    whole (chains x)=(x.map whole).prod := by
  have e (p:S) (q:List S) :
    whole (q.foldl (fun x b=>times (x,b)) p)= whole p*(q.map whole).prod := by
    induction q generalizing p with
    | nil=>simp
    | cons a q ih=>simp [List.foldl_cons,ih,mul_assoc]
  change whole (List.foldl (fun x b=>times (x,b)) (false,[true]) x)=_
  rw [e,show whole (false,[true])=1 from rfl,one_mul]

def stepper (x:S×Tally) := chains (x.2.map fun _=>x.1)
@[fun_prop] theorem stepP : Poly stepper := by
  have p : Poly (fun x:S×Tally=> x.2.map fun _=>x.1) := Easy.exchange.poly.compose Packed.chamber
  exact p.compose chainsP
theorem steps_v (x:S) (q:Tally) :
    whole (stepper (x,q))=(whole x)^q.length := by simp [stepper,chainsV,List.map_const']
end Brief

end IntegerMultiplication
end Computability
end OAI
