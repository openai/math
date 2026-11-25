import OAI.Computability.BorderVNP.CoverDeckEnumerationCost
import OAI.Computability.RationalHitting.SignedArithmetic

/-!
# Bit cost of modular tile-address multiplication

The word-operation count of Lemma 5.1 is output-linear up to a polynomial in
the cover depth. Each modular quaternion multiplication can be carried out by
one fixed binary stack program in polynomially many bit steps. Its inputs
are the positive modulus and the eight residue coordinates in binary.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open RationalHitting RationalHitting.StackLanguage Function

private def remainderRoutine : Program (Fin 10) :=
  .seq divide (.seq (clear 7) (clear 5))

private theorem eval_remainder (a m : ℕ) (hm : 0 < m) :
    ∃ t ≤ 400*(a.bits.length+m.bits.length+1)^2,
      Eval remainderRoutine (both (0 : Fin 10) 5 a.bits m.bits) (single 0 (a%m).bits) t := by
  let s := both (0 : Fin 10) 5 a.bits m.bits
  obtain ⟨t,ht,he⟩ := eval_divide s (by simp [s,divScratch,both,single])
    (by simp [s,both,single]) (by simp [s,both,single]) (by simpa [s] using hm)
  simp only [s,both_first (by decide : (0 : Fin 10) ≠ 5),both_second,wordValue_bits] at ht he
  let u := update (update s 0 (a%m).bits) 7 (a/m).bits
  let v := update u 7 []
  have hc := Eval.seq he (Eval.seq (eval_clear 7 u) (eval_clear 5 v))
  have hend : update v 5 [] = single 0 (a%m).bits := by
    funext k
    by_cases h0 : k = 0 <;> by_cases h5 : k = 5 <;> by_cases h7 : k = 7 <;>
      simp_all [v,u,s,both,single]
  rw [hend] at hc
  refine ⟨_,?_,hc⟩
  simp [v,u,s]
  have hq := nat_bits_mono (Nat.div_le_self a m)
  have hprod : (a.bits.length+1)*(m.bits.length+1) ≤
      (a.bits.length+m.bits.length+1)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  nlinarith only [ht,hprod,hq,Nat.zero_le a.bits.length,Nat.zero_le m.bits.length,
    Nat.zero_le (a.bits.length^2),Nat.zero_le (m.bits.length^2)]

/-- Binary long division on the existing stack machine computes the canonical
remainder with a quadratic bit-step bound. -/
theorem modularRemainder_poly : Poly (fun p : ℕ × {n : ℕ // 0 < n} => p.1 % p.2.val) := by
  refine ⟨Procedure.fromBinary remainderRoutine 0 5 0 (by decide)
    (400*TimeBound.variable^2) ?_ ?_⟩
  · intro a b
    change ∃ t ≤ 400*(a.bits.length+b.val.bits.length+1)^2,
      Eval remainderRoutine (both 0 5 a.bits b.val.bits) (single 0 (a%b.val).bits) t
    exact eval_remainder a b.val b.2
  · intro a b
    have h := nat_bits_mono (Nat.mod_le a b.val)
    change (a%b.val).bits.length ≤ 400*(a.bits.length+b.val.bits.length+1)^2
    have hh : a.bits.length+b.val.bits.length+1 ≤ (a.bits.length+b.val.bits.length+1)^2 :=
      Nat.le_self_pow (by decide) _
    omega

attribute [local fun_prop] modularRemainder_poly

/-- Four natural coordinates in the binary residue representation. -/
abbrev BinaryCoords := ℕ × ℕ × ℕ × ℕ

/-- Inputs to one uniform modular quaternion product. -/
abbrev ProductInput := {n : ℕ // 0 < n} × BinaryCoords × BinaryCoords

private def negDigit (m b : ℕ) := ((m : ℤ) - (b : ℤ)).natAbs

@[local fun_prop] private theorem negDigit_poly : Poly (fun t : ℕ × ℕ => negDigit t.1 t.2) :=
  Poly.natDifferenceAbs

/-- Multiply modular quaternion coordinates by natural additions and
multiplications, using the additive inverse of a reduced second-operand
coordinate for each negative term. -/
def binaryProduct (p : ProductInput) : BinaryCoords :=
  let m := p.1
  let x := p.2.1
  let y := p.2.2
  let nz := negDigit m.val
  ((x.1*y.1 + 2*x.2.1*y.2.1 + 3*x.2.2.1*y.2.2.1 + 6*x.2.2.2*nz y.2.2.2) % m.val,
   (x.1*y.2.1 + x.2.1*y.1 + 3*x.2.2.1*nz y.2.2.2 + 3*x.2.2.2*y.2.2.1) % m.val,
   (x.1*y.2.2.1 + 2*x.2.1*y.2.2.2 + x.2.2.1*y.1 + 2*x.2.2.2*nz y.2.1) % m.val,
   (x.1*y.2.2.2 + x.2.1*y.2.2.1 + x.2.2.1*nz y.2.1 + x.2.2.2*y.1) % m.val)

/-- A single bit-stack program computes the modular product, with a
polynomial bound uniform in the modulus and its binary operands. -/
theorem binaryProduct_poly : Poly binaryProduct := by
  have rem {f : ProductInput → ℕ} (hf : Poly f) :
      Poly (fun p => f p % p.1.val) := modularRemainder_poly.comp (hf.pair Poly.fst)
  unfold binaryProduct
  exact Poly.pair (rem (by fun_prop))
    (Poly.pair (rem (by fun_prop)) (Poly.pair (rem (by fun_prop))
      (rem (by fun_prop))))

/-- Extract the four natural representatives of a modular address. -/
def binaryCoords (l : ℕ) (x : Address l) : BinaryCoords :=
  (x.re.val,x.imI.val,x.imJ.val,x.imK.val)

/-- The stack program's output is exactly the canonical four-residue encoding
of the quaternion product used by the enumerator. -/
theorem binaryProduct_correct (l : ℕ) (x y : Address l) :
    binaryProduct (⟨7^l, by positivity⟩,binaryCoords l x,binaryCoords l y) =
      binaryCoords l (x*y) := by
  let n := 7^l
  have hn : 0 < n := by dsimp [n]; positivity
  let : NeZero n := ⟨hn.ne'⟩
  have minus (v : ZMod (7^l)) : (negDigit (7^l) v.val : ZMod (7^l)) = -v := by
    have hv := ZMod.val_lt v
    have hi : 0 ≤ (n : ℤ) - (v.val : ℤ) := by omega
    have hcast : (((n : ℤ) - (v.val : ℤ)).natAbs : ℤ) = (n : ℤ) - (v.val : ℤ) := by
      rw [Int.natCast_natAbs,abs_of_nonneg hi]
    have hh := congrArg (fun z : ℤ => (z : ZMod n)) hcast
    change (((n : ℤ) - (v.val : ℤ)).natAbs : ZMod n) = -v
    simpa only [Int.cast_natCast,Int.cast_sub,ZMod.natCast_self,zero_sub,ZMod.natCast_zmod_val] using hh
  have hc (a : ℕ) (z : ZMod n) (h : (a : ZMod n) = z) : a % n = z.val := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val h
  rcases x with ⟨a,b,c,d⟩
  rcases y with ⟨u,v,w,z⟩
  apply Prod.ext
  · apply hc
    simp only [binaryCoords, Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
      ZMod.natCast_zmod_val,minus,QuaternionAlgebra.mk_mul_mk]
    ring
  · apply Prod.ext
    · apply hc
      simp only [binaryCoords, Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
        ZMod.natCast_zmod_val,minus,QuaternionAlgebra.mk_mul_mk]
      ring
    · apply Prod.ext
      all_goals
        apply hc
        simp only [binaryCoords, Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
          ZMod.natCast_zmod_val,minus,QuaternionAlgebra.mk_mul_mk]
        ring

/-- The canonical binary product input has length linear in the cover depth. -/
theorem binaryProduct_input_length (l : ℕ) (x y : Address l) :
    (code ((⟨7^l, by positivity⟩, binaryCoords l x, binaryCoords l y) : ProductInput)).length
      + 1 ≤ 80*(l+1) := by
  have bits (z : ZMod (7^l)) : z.val.bits.length ≤ 3*l := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact residue_lt_bit_bound l z
  have bm : (7^l).bits.length ≤ 3*l+1 := by
    rw [Nat.size_eq_bits_len,Nat.size_le,pow_succ]
    have hh := Nat.pow_le_pow_left (show 7 ≤ 2^3 by decide) l
    rw [← pow_mul] at hh
    have hp : 0 < 2^(3*l) := by positivity
    omega
  simp only [binaryCoords,prod_code_length,nat_code_length]
  change 2 * (7^l).bits.length + 1 + _ + 1 ≤ _
  have b1 := bits x.re
  have b2 := bits x.imI
  have b3 := bits x.imJ
  have b4 := bits x.imK
  have b5 := bits y.re
  have b6 := bits y.imI
  have b7 := bits y.imJ
  have b8 := bits y.imK
  omega

/-- One fixed finite stack program realizes every modular multiplication in
the listing algorithm, with a polynomial bit-step bound in the cover depth.
The output is the exact coordinate encoding of the product. -/
theorem binaryProduct_bit_steps :
    ∃ p : Procedure code code binaryProduct,
      ∀ (l : ℕ) (x y : Address l), ∃ t ≤ p.bound.eval (80*(l+1)),
        Eval p.program
          (single p.input (code ((⟨7^l, by positivity⟩, binaryCoords l x, binaryCoords l y)
            : ProductInput)))
          (single p.output (code (binaryCoords l (x*y)))) t := by
  obtain ⟨p⟩ := binaryProduct_poly
  refine ⟨p,?_⟩
  intro l x y
  obtain ⟨t,ht,he⟩ := p.correct (⟨7^l, by positivity⟩, binaryCoords l x, binaryCoords l y)
  rw [binaryProduct_correct] at he
  exact ⟨t, ht.trans (p.bound.monotone (binaryProduct_input_length l x y)), he⟩

end Cover

end BorderVNP
end Computability
end OAI
