import OAI.Computability.IntegerMultiplication.Carry.Remainder
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Sqrt

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Carry
open Code Bits

def flash (i:Tally):Word:= fill false i ++ [true]
@[simp] theorem flash_v (i:Tally) : value (flash i)=2^i.length := by simp [flash,fill,value_append]
@[fun_prop] theorem easy_flash : Easy flash := by unfold flash; fun_prop

def rain (n:Tally):List Word:=
  ((Iter.lineup n).map flash).reverse
@[fun_prop] theorem rainPoly : Poly rain := by
  unfold rain
  exact (Iter.poly_line.compose (easy_flash.mapping.poly)).rev

theorem rain_rule (i:ℕ):
    rain (tally (i+1))=flash (tally i)::rain (tally i) := by
  unfold rain
  simp only [Iter.lined,List.ofFn_succ',Fin.val_last,Fin.val_castSucc,List.concat_eq_append,List.map_append,List.map_cons,List.map_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append]

private def guess (i: Word×Word×Word) := Bits.add i.2

def exam (i:Word × Word × Word) : Word :=
  bif lt_ (i.1,times0 (guess i,guess i)) then i.2.1 else guess i
@[fun_prop] theorem checks : Poly exam := by
  unfold exam guess; fun_prop

private theorem exam_len (a x q:Word) :
    (exam (a,x,q)).length ≤ x.length+q.length+1 := by
  unfold exam; cases h:lt_ _ <;> simp [guess]; omega
private theorem exam_size (a x q:Word) :
    size (exam (a,x,q)) ≤ size x+4*(size a+size q) := by
  simp only [size_word]; have := exam_len a x q; omega

def rescue (x:Word):Word := trek exam (rain (ruler x),x,[])

@[fun_prop] theorem rescuePoly : Poly rescue := by
  have p:= (Easy.ruler (X:=Bool) Easy.identity).poly.compose rainPoly
  exact (show Poly (fun x:Word=> (rain (ruler x),x,([]:Word))) from by fun_prop (maxTransitionDepth:=3)).compose (polyTrek _ checks 4 exam_size)

private theorem single (a x:Word) (p:ℕ) (n _n' m:ℕ)
    (e : value a=n) (v : value x=m)
    (h : m≤n.sqrt) (q : n.sqrt < m+2^(p+1)) :
    let y:= value (exam (a,x,flash (tally p)))
    y≤n.sqrt ∧ n.sqrt<y+2^p := by
  unfold exam guess
  dsimp only
  rw [lt_r,tm_value, add_val,e,v,flash_v,tally_length]
  by_cases k : n < (m+2^p)*(m+2^p)
  · rw [decide_eq_true k,Bool.cond_true,v]
    exact ⟨h,Nat.sqrt_lt.mpr k⟩
  rw [decide_eq_false k,Bool.cond_false, Bits.add_val,flash_v,tally_length,v]
  rw [pow_succ] at q
  exact ⟨Nat.le_sqrt.mpr (le_of_not_gt k),by omega⟩

private theorem allSteps (p:ℕ) (a x:Word)
    (h : value x ≤ (value a).sqrt) (q : (value a).sqrt < value x+2^p) :
    value (trek exam (rain (tally p),a,x))=(value a).sqrt := by
  induction p generalizing x with
  | zero=>
    change value x = _
    rw [pow_zero] at q; omega
  | succ p ih=>
    rw [rain_rule]
    change value (trek exam (rain (tally p),a,exam (a,x,flash (tally p))))=_
    have u:= single a x p _ 0 _ rfl rfl h q
    exact ih _ u.1 u.2
theorem rescued (x) :
    value (rescue x)=(value x).sqrt := by
  unfold rescue
  rw [show ruler x=tally x.length by simp [tally,ruler]]
  apply allSteps x.length x []
  · simp
  rw [value_nil,Nat.zero_add]
  exact (Nat.sqrt_le_self _).trans_lt (value_lt _)
end Carry

end IntegerMultiplication
end Computability
end OAI
