import OAI.Computability.IntegerMultiplication.Carry.Square

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Carry
open Code Bits

def count (x:Word) (t: List Word) : Word :=
  trek (fun i:Unit × Word × Word=> times0 i.2) (t,(),x)
theorem countPoly : Poly (fun i : Word × List Word=> count i.1 i.2) := by
  exact Poly.compose (show Poly (fun i : Word × List Word=> (i.2,(),i.1)) from by fun_prop)
    (polyTrek _ (by fun_prop) 1 (by
      intro _ x y
      simp only [size_word,tm_length,one_mul]; omega))

theorem countVal (x:Word) (l:List Word) :
    value (count x l) = value x * (l.map Bits.value).prod := by
  induction l generalizing x with
  | nil=> simp; rfl
  | cons a l ih =>
    change value (count (times0 (x,a)) l) = _
    rw [ih,tm_value,List.map_cons,List.prod_cons,Nat.mul_assoc]

def fires (p:Word × Tally) : Word :=
  count [true] (p.2.map fun _=>p.1)

@[fun_prop] theorem firesPoly : Poly fires := by
  have v : Poly (fun p:Word × Tally=>p.2.map fun _=>p.1) :=
    Easy.exchange.poly.compose Packed.chamber
  exact ((Code.Poly.const ([true]:Word)).pair v).compose countPoly

theorem fires_r (x:Word) (u:Tally) :
    value (fires (x,u))=value x^u.length := by simp [fires,countVal,List.map_const']

-- factors n! via formula list descending
def chain_ (t:Tally) :=
  (((Iter.lineup t).map (fun i => ()::i)).map (fun s => born s.length)).reverse

@[fun_prop] theorem chainPoly : Poly chain_ :=
  ((Iter.poly_line.compose (Easy.mapping (f:=fun i:Tally=> ()::i) (by fun_prop)).poly).compose
    (easy_chart.mapping.poly)).rev
theorem chain_rule (p) :
    chain_ (tally (p+1)) = born (p+1)::chain_ (tally p) := by
  unfold chain_
  simp only [Iter.lined,List.ofFn_succ',Fin.val_castSucc,List.concat_eq_append,
    Fin.val_last,List.map_append,List.map_cons,List.length_cons,tally_length,
    List.map_nil,List.reverse_append]
  simp

def factors (t:Tally) := count [true] (chain_ t)
@[fun_prop] theorem factorCost : Poly factors :=
  ((Code.Poly.const ([true]:Word)).pair chainPoly).compose countPoly
@[simp] theorem factors_v (p):
    value (factors (tally p))=Nat.factorial p := by
  unfold factors; rw [countVal]
  simp only [value_cons,d1,value_nil,Nat.mul_zero,Nat.add_zero, one_mul]
  induction p with
  | zero=>rfl
  | succ p ih=> rw [chain_rule,List.map_cons,List.prod_cons,birthValue,ih,Nat.factorial_succ]
end Carry

end IntegerMultiplication
end Computability
end OAI
