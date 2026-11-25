import OAI.Computability.NearSquareRoot.InterchangeROMAffineMask

/-! # The fixed binary modulus program for variable radix and address width -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAffineMask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry IntegerMultiplication.Bits

private def timesBase (p : Word × Word × Unit) := times0 (p.1,p.2.1)

private theorem timesBase_poly : Poly timesBase := by unfold timesBase; fun_prop

private theorem carry_power : Poly (trek timesBase) := by
  apply polyTrek timesBase timesBase_poly 2
  intro a b c
  simp only [timesBase,size_word,tm_length]
  omega

private def digitsPower (x : Tally × Tally) :=
  trek timesBase (x.2,born x.1.length,[true])

private theorem digitsPower_poly : Poly digitsPower :=
  (show Poly (fun x : Tally × Tally => (x.2,born x.1.length,([true] : Word))) from
    Easy.snd.poly.pair ((Easy.fst.compose easy_chart).poly.pair ((Easy.const _).poly))).compose carry_power

private theorem digitsPower_value (p f : Tally) :
    value (digitsPower (p,f)) = p.length ^ f.length := by
  have go (s : Word) (z : Tally) (b : Word) :
      value (trek timesBase (z,b,s)) = value s * value b ^ z.length := by
    induction z generalizing s with
    | nil => simp [trek]
    | cons u z ih =>
      change value (trek timesBase (z,b,times0 (b,s))) = _
      rw [ih,tm_value,List.length_cons,pow_succ]
      ring
  simp only [digitsPower,go,birthValue]
  simp [value,digit]

private theorem cut_born (s : Word) : cut s = born (value s) := by
  induction s with
  | nil => simp [cut]
  | cons b s ih =>
    rw [cuts,ih]
    cases e : value s with
    | zero =>
      have one : born 1 = [true] := by rw [birth (by decide : 0<1)]; simp [parity]
      rw [value_cons,e]; cases b <;> simp [digit,tack,one]
    | succ n =>
      have pos : 0 < value (b::s) := by rw [value_cons,e]; omega
      rw [birth pos]
      have nz : (born (n+1)).isEmpty = false := by simp [birth (Nat.succ_pos n)]
      have bite : parity (digit b+2*(n+1))=b := by cases b <;> simp [digit,parity]
      have half : (digit b+2*(n+1))/2=n+1 := by have := digit_le b; omega
      simp only [tack,nz,Bool.false_and,Bool.cond_false,value_cons,e,bite,half]

/-- The binary modulus occupies at most one initial bit and one base word
per field digit, including nonminimal multiplication output before trimming. -/
theorem modulus_size (p f : ℕ) : size (born (p^f)) ≤ 2*(f*p+1)+1 := by
  have go (s : Word) (z : Tally) (b : Word) :
      (trek timesBase (z,b,s)).length = s.length+z.length*b.length := by
    induction z generalizing s with
    | nil => simp [trek]
    | cons u z ih =>
      change (trek timesBase (z,b,times0 (b,s))).length = _
      rw [ih,tm_length,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  have small := (cut_v (digitsPower (tally p,tally f))).2.1
  rw [cut_born,digitsPower_value] at small
  simp only [digitsPower,go,tally_length,List.length_cons,List.length_nil] at small
  have bound := Nat.mul_le_mul_left f (birthLen p)
  rw [size_word]
  omega

/-- The input consists of two unary header fields. Only the binary value
of the radix power is materialized. -/
def modulus (x : Tally × Tally) : Word := cut (digitsPower x)

theorem modulus_poly : Poly modulus := digitsPower_poly.compose polyCut

@[simp] theorem modulus_tally (p f : ℕ) : modulus (tally p,tally f) = born (p^f) := by
  simp [modulus,cut_born,digitsPower_value]

end InterchangeAffineMask

end NearSquareRoot
end Computability
end OAI
