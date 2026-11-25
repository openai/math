import OAI.ThreeFlat.RAM.PhysicalPinFields

namespace OAI
/-! # The instruction expression implements the shape's row decoder -/

namespace ThreeFlat.RAM.PhysicalPinsExpr

variable {n w : ℕ} (s : Shape) (m : ℕ → ℕ) (v : Fin n → ℕ)
local notation "E" => nat (w:=w) s m v

private theorem nAdd (x y : Formula n) : E (add x y) = E x+E y := rfl
private theorem nSub (x y : Formula n) : E (sub x y) = E x-E y := rfl
private theorem nMul (x y : Formula n) : E (mul x y) = E x*E y := rfl
private theorem nDiv (x y : Formula n) : E (div x y) = E x/E y := rfl
private theorem nMod (x y : Formula n) : E (rem x y) = E x%E y := rfl
private theorem nShr (x y : Formula n) : E (.op .shiftRight x y) =
    (if E y<w then E x>>>E y else 0) := rfl
private theorem nLt (x y a b : Formula n) : E (lt x y a b) =
    (if E x<E y then E a else E b) := by simp [nat,Formula.natural,natTest]
private theorem nEq (x y a b : Formula n) : E (eqz x y a b) =
    (if E x=E y then E a else E b) := by simp [nat,Formula.natural,natTest]
private theorem nLit (x : ℕ) : E (L x) = x := rfl
private theorem nParam (x : Param) : E (A x) = s.words x := rfl
private theorem nLoad (x : Formula n) : E (.load x) = m (E x) := rfl

theorem nat_pin (i j : Formula n) :
    E (pinFormula i j) = s.decode w m (E i) (E j) := by
  have hp : s.advice+s.teamBits+s.timeBits+s.parameterBits+s.bits+s.bits+s.bits+s.bits =
      s.plen := by simp [Shape.plen,Diagonal.ApproximateImage.pinCount,Nat.add_assoc]
  have size : (s.inside+1)*s.teams*s.plen=s.area := rfl
  by_cases h : E j-s.area<s.halfBits
  · have hb := Nat.not_le_of_lt h
    simp only [pinFormula,nLt,nEq,nat_endpoint,nat_middle,nat_active,nat_half,nAdd,nSub,
      nMul,nDiv,nMod,nShr,nParam,nLit,nLoad,Shape.words,Nat.add_sub_cancel,hp,
      size,Shape.decode,Shape.ticking,Shape.digit,Shape.passive,h,hb,decide_false,ite_true]
  · have hb := Nat.le_of_not_gt h
    simp only [pinFormula,nLt,nEq,nat_endpoint,nat_middle,nat_active,nat_half,nAdd,nSub,
      nMul,nDiv,nMod,nShr,nParam,nLit,nLoad,Shape.words,Nat.add_sub_cancel,hp,
      size,Shape.decode,Shape.ticking,Shape.digit,Shape.passive,h,hb,decide_true,ite_false]

theorem nat_copy (cell col : Formula n) :
    E (copyFormula cell col) = m (s.templateBase+11*E cell+E col) := rfl

end ThreeFlat.RAM.PhysicalPinsExpr

end OAI
