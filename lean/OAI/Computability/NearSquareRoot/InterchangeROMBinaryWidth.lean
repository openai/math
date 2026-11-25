import OAI.Computability.NearSquareRoot.InterchangeROMAffineModulus
import OAI.Computability.IntegerMultiplication.Carry.Square
import Mathlib.Data.Nat.Log

/-! # Choosing the positive native field width from a binary packet header

The same polynomial tree program accepts the unary radix and moving width as
input. Its intermediate powers are maintained in binary.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBinary

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits IntegerMultiplication.Carry

/-- Smallest positive native width that contains all binary field values. -/
def width (b n : ℕ) := max 1 (Nat.clog b (2^n))

private abbrev State := (Tally × Tally) × Tally × Unit

private def advance (z : State) : Tally :=
  bif more (flash z.1.2, InterchangeAffineMask.modulus (z.1.1,z.2.1))
  then () :: z.2.1 else z.2.1

private theorem advance_poly : Poly advance := by
  apply Poly.choose
  · exact (((show Poly (fun z : State => z.1.2) by fun_prop).compose easy_flash.poly).pair
      ((show Poly (fun z : State => (z.1.1,z.2.1)) by fun_prop).compose
        InterchangeAffineMask.modulus_poly)).compose (easy_more Easy.identity).poly
  · fun_prop
  · fun_prop

/-- Both components of the argument are unary, so the result is immediately
usable as a field descriptor by the native request compiler. -/
def chooseWidth (x : Tally × Tally) : Tally := trek advance (x.2,x,[()])

@[fun_prop] theorem chooseWidth_poly : Poly chooseWidth := by
  have h := polyTrek advance advance_poly 2 (fun p x y => by
    unfold advance
    dsimp only
    cases y
    have unit_size : size () = 1 := rfl
    cases more (flash p.2,InterchangeAffineMask.modulus (p.1,x)) <;> simp [size_tally,size_prod,unit_size]; omega)
  exact (show Poly (fun x : Tally × Tally => (x.2,x,[()])) by fun_prop).compose h

private theorem advanced (b n : ℕ) (x : Tally) (hb : 2 ≤ b) :
    (advance ((tally b,tally n),x,())).length =
      if x.length < Nat.clog b (2^n) then x.length+1 else x.length := by
  have hx : InterchangeAffineMask.modulus (tally b,x) = born (b^x.length) := by
    simpa only [recover_tally] using InterchangeAffineMask.modulus_tally b x.length
  have h : (more (flash (tally n),InterchangeAffineMask.modulus (tally b,x)) = true) ↔
      x.length < Nat.clog b (2^n) := by
    rw [more_lt,hx,birthValue,flash_v,tally_length,Nat.lt_clog_iff_pow_lt hb]
  unfold advance
  cases e : more (flash (tally n),InterchangeAffineMask.modulus (tally b,x)) <;> simp_all

@[simp] theorem chooseWidth_tally {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    chooseWidth (tally b,tally n) = tally (width b n) := by
  let c := Nat.clog b (2^n)
  have h (q x : Tally) : (trek advance (q,(tally b,tally n),x)).length =
      max x.length (min (x.length+q.length) c) := by
    induction q generalizing x with
    | nil => simp [trek]
    | cons a q ih =>
      cases a
      change (trek advance (q,(tally b,tally n),advance ((tally b,tally n),x,()))).length = _
      rw [ih,advanced b n x hb,List.length_cons]
      dsimp only [c]
      split <;> omega
  have lower : c ≤ n := Nat.clog_le_of_le_pow (Nat.pow_le_pow_left hb n)
  have he := h (tally n) [()]
  simp only [tally_length,List.length_cons,List.length_nil] at he
  rw [show chooseWidth (tally b,tally n) = tally (chooseWidth (tally b,tally n)).length from
    (recover_tally _).symm]
  congr 1
  change (trek advance (tally n,(tally b,tally n),[()])).length = max 1 c
  omega

theorem width_bounds {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    0 < width b n ∧ width b n ≤ n+1 ∧ 2^n ≤ b^(width b n) ∧ b^(width b n) ≤ b * 2^n := by
  let c := Nat.clog b (2^n)
  have hc : c ≤ n := Nat.clog_le_of_le_pow (Nat.pow_le_pow_left hb n)
  change 0 < max 1 c ∧ max 1 c ≤ n+1 ∧ _ ≤ b^max 1 c ∧ b^max 1 c ≤ _
  refine ⟨by omega,by omega,(Nat.le_pow_clog hb _).trans (Nat.pow_le_pow_right (by omega) (le_max_right 1 c)),?_⟩
  by_cases h : c ≤ 1
  · rw [max_eq_left h,pow_one]
    exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  · rw [max_eq_right (by omega : 1 ≤ c)]
    obtain ⟨k,hk⟩ : ∃ k, c = k+1 := ⟨c-1,by omega⟩
    have hk' : k < Nat.clog b (2^n) := by change k < c; omega
    have hf := Nat.pow_lt_of_lt_clog hk'
    rw [hk,pow_succ']
    exact Nat.mul_le_mul_left b hf.le

end InterchangeROMBinary

end NearSquareRoot
end Computability
end OAI
