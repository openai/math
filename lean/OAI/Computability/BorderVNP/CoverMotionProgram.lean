import OAI.Computability.BorderVNP.CoverMotionTable

/-!
# Bit implementation of the finite quaternion motion table

A fixed positive denominator and a finite table of signed integral entries
are compiled into one stack program. On input the cover depth and four binary
address fields, the program evaluates the exact correction using polynomially
many bit steps in the depth. The output fields are canonical residues.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open RationalHitting RationalHitting.StackLanguage Function

private abbrev Modulus := {n : ℕ // 0 < n}

private def quotientRoutine : Program (Fin 10) := .seq divide (.seq (clear 0) (clear 5))

private theorem eval_quotient (a m : ℕ) (hm : 0 < m) :
    ∃ t ≤ 400*(a.bits.length+m.bits.length+1)^2,
      Eval quotientRoutine (both (0 : Fin 10) 5 a.bits m.bits) (single 7 (a/m).bits) t := by
  let s := both (0 : Fin 10) 5 a.bits m.bits
  obtain ⟨t,ht,he⟩ := eval_divide s (by simp [s,divScratch,both,single])
    (by simp [s,both,single]) (by simp [s,both,single]) (by simpa [s] using hm)
  simp only [s,both_first (by decide : (0 : Fin 10) ≠ 5),both_second,wordValue_bits] at ht he
  let u := update (update s 0 (a%m).bits) 7 (a/m).bits
  let v := update u 0 []
  have hc := Eval.seq he (Eval.seq (eval_clear 0 u) (eval_clear 5 v))
  have hend : update v 5 [] = single 7 (a/m).bits := by
    funext k
    by_cases h0 : k = 0 <;> by_cases h5 : k = 5 <;> by_cases h7 : k = 7 <;>
      simp_all [v,u,s,both,single]
  rw [hend] at hc
  refine ⟨_,?_,hc⟩
  simp [v,u,s]
  have hq := nat_bits_mono (Nat.mod_le a m)
  have hprod : (a.bits.length+1)*(m.bits.length+1) ≤
      (a.bits.length+m.bits.length+1)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  nlinarith only [ht,hprod,hq,Nat.zero_le a.bits.length,Nat.zero_le m.bits.length,
    Nat.zero_le (a.bits.length^2),Nat.zero_le (m.bits.length^2)]

/-- Binary long division by a positive denominator is polynomial-time on the stack machine. -/
theorem quotient_poly : Poly (fun p : ℕ × Modulus => p.1/p.2.val) := by
  refine ⟨Procedure.fromBinary quotientRoutine 0 5 7 (by decide)
    (400*TimeBound.variable^2) ?_ ?_⟩
  · intro a b
    change ∃ t ≤ 400*(a.bits.length+b.val.bits.length+1)^2,
      Eval quotientRoutine (both 0 5 a.bits b.val.bits) (single 7 (a/b.val).bits) t
    exact eval_quotient a b.val b.2
  · intro a b
    have h := nat_bits_mono (Nat.div_le_self a b.val)
    change (a/b.val).bits.length ≤ 400*(a.bits.length+b.val.bits.length+1)^2
    have hh : a.bits.length+b.val.bits.length+1 ≤ (a.bits.length+b.val.bits.length+1)^2 :=
      Nat.le_self_pow (by decide) _
    omega

private theorem positive_remainder {A : Type} [Coding A] {f : A → ℕ} {m : A → Modulus}
    (hf : Poly f) (hm : Poly m) : Poly (fun a => f a % (m a).val) :=
  modularRemainder_poly.comp (hf.pair hm)

private theorem storedInt_poly (z : ℤ) : Poly (fun m : Modulus => storedInt m.val z) := by
  have hr : Poly (fun m : Modulus => z.natAbs%m.val) :=
    positive_remainder (StackLanguage.Poly.const _) Poly.id
  by_cases hz : z < 0
  · have hd := Poly.natDifferenceAbs.comp ((Poly.subtypeVal _).pair hr)
    have hs : Poly (fun m : Modulus => m.val - z.natAbs%m.val) := hd.of_eq (by
      intro m
      have h := Nat.mod_lt z.natAbs m.2
      have he : ((m.val - z.natAbs%m.val : ℕ) : ℤ) = (m.val:ℤ) - (z.natAbs%m.val:ℕ) :=
        Nat.cast_sub h.le
      rw [← he,Int.natAbs_natCast])
    simpa only [storedInt,hz,↓reduceIte] using positive_remainder hs Poly.id
  · simpa only [storedInt,hz,↓reduceIte] using hr

private theorem storedCoords_poly (z : Order) : Poly (fun m : Modulus => storedCoords m.val z) :=
  (storedInt_poly _).pair ((storedInt_poly _).pair ((storedInt_poly _).pair (storedInt_poly _)))

private theorem lowCoords_poly (m : Modulus) : Poly (lowCoords m.val) := by
  have cut {f : BinaryCoords → ℕ} (hf : Poly f) : Poly (fun z => f z % m.val) :=
    positive_remainder hf (StackLanguage.Poly.const m)
  exact (cut Poly.fst).pair ((cut (by fun_prop)).pair ((cut (by fun_prop)).pair (cut (by fun_prop))))

private theorem coord_eq_poly (v : BinaryCoords) : Poly (fun z : BinaryCoords => decide (z = v)) := by
  have bit {f : BinaryCoords → ℕ} (hf : Poly f) (n : ℕ) : Poly (fun z => decide (f z = n)) :=
    (Poly.natZero.comp (Poly.natDifferenceAbs.comp (hf.pair (StackLanguage.Poly.const n)))).of_eq (by intro z; simp [sub_eq_zero])
  have conj {f g : BinaryCoords → Bool} (hf : Poly f) (hg : Poly g) :
      Poly (fun x => f x && g x) := Poly.boolAnd.comp (hf.pair hg)
  have h := conj (bit Poly.fst v.1) (conj (bit (f := fun x => x.2.1) (by fun_prop) v.2.1)
    (conj (bit (f := fun x => x.2.2.1) (by fun_prop) v.2.2.1)
      (bit (f := fun x => x.2.2.2) (by fun_prop) v.2.2.2)))
  apply h.of_eq
  rintro ⟨a,b,c,d⟩
  rcases v with ⟨u,v,w,z⟩
  by_cases ha : a=u <;> by_cases hb : b=v <;> by_cases hc : c=w <;> by_cases hd : d=z <;> simp [ha,hb,hc,hd]

private theorem lookup_poly (table : List (BinaryCoords × Order)) :
    Poly (fun p : Modulus × BinaryCoords => storedCoords p.1.val (lookupInverse p.2 table)) := by
  induction table with
  | nil => exact (storedCoords_poly 1).comp Poly.fst
  | cons e t ih =>
    apply (Poly.cond ((coord_eq_poly e.1).comp Poly.snd) ((storedCoords_poly e.2).comp Poly.fst)
      ih).of_eq
    intro p
    by_cases h : p.2 = e.1 <;> simp [lookupInverse,h]

private theorem divideCoords_poly (m : Modulus) : Poly (divideCoords m.val) := by
  have cut {f : BinaryCoords → ℕ} (hf : Poly f) : Poly (fun z => f z / m.val) :=
    quotient_poly.comp (hf.pair (StackLanguage.Poly.const m))
  exact (cut Poly.fst).pair ((cut (by fun_prop)).pair ((cut (by fun_prop)).pair (cut (by fun_prop))))

/-- A binary polynomial-time stack procedure evaluates the entire fixed table,
including signed constant reduction, lookup, multiplication and division. -/
theorem tableCorrection_poly (a : ℕ) (u v : Order) (t : List (BinaryCoords × Order)) :
    Poly (fun p : Modulus × BinaryCoords => tableCorrection a u v t p.1 p.2) := by
  have prod {f h : Modulus × BinaryCoords → BinaryCoords} (hf : Poly f) (hh : Poly h) :
      Poly (fun p => binaryProduct (p.1, f p, h p)) :=
    binaryProduct_poly.comp (Poly.fst.pair (hf.pair hh))
  have hi := (lookup_poly t).comp (Poly.fst.pair ((lowCoords_poly ⟨7^(1+2*a),by positivity⟩).comp Poly.snd))
  exact (divideCoords_poly ⟨7^(2*a),by positivity⟩).comp
    (prod (prod (prod ((storedCoords_poly u).comp Poly.fst) Poly.snd) hi)
      ((storedCoords_poly v).comp Poly.fst))

private theorem high_modulus_poly (a : ℕ) :
    Poly (fun d : Unary => (⟨7^(d.val+2*a), by positivity⟩ : Modulus)) := by
  have hp : Poly (fun d : Unary => (7:ℤ)^d.val) := Poly.intPow.comp ((StackLanguage.Poly.const 7).pair Poly.id)
  have hn : Poly (fun d : Unary => (7:ℕ)^d.val) :=
    (Poly.intAbs.comp hp).of_eq (by intro d; simp)
  have h := Poly.natMul.comp (hn.pair (StackLanguage.Poly.const (7^(2*a))))
  exact (h.of_eq (by intro d; exact (pow_add 7 d.val (2*a)).symm)).subtypeMk
    (fun _ => by positivity)

/-- Input to the running machine consists solely of the output depth and the
four binary coordinates of the input tile. -/
def correctionAt (a : ℕ) (u v : Order) (t : List (BinaryCoords × Order))
    (input : Unary × BinaryCoords) : BinaryCoords :=
  tableCorrection a u v t ⟨7^(input.1.val+2*a), by positivity⟩ input.2

private theorem correctionAt_poly (a : ℕ) (u v : Order) (t : List (BinaryCoords × Order)) :
    Poly (correctionAt a u v t) := by
  let next (i : Unary × BinaryCoords) : Modulus × BinaryCoords :=
    (⟨7^(i.1.val+2*a),by positivity⟩,i.2)
  have step : Poly next := Poly.pair ((high_modulus_poly a).comp Poly.fst) Poly.snd
  have h := (tableCorrection_poly a u v t).comp step
  exact h.of_eq (fun _ => rfl)

/-- The unary depth and the four modular coordinates fit in the linear motion-input budget. -/
theorem motionDeck_input_length (d a : ℕ) (x : Address (d+2*a)) :
    (code ((⟨d⟩,binaryCoords (d+2*a) x) : Unary × BinaryCoords)).length+1 ≤
      30*(d+2*a+1) := by
  have bits (z : ZMod (7^(d+2*a))) : z.val.bits.length ≤ 3*(d+2*a) := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact residue_lt_bit_bound _ z
  simp only [binaryCoords,prod_code_length,unary_code_length,nat_code_length]
  have b1 := bits x.re
  have b2 := bits x.imI
  have b3 := bits x.imJ
  have b4 := bits x.imK
  omega

/-- For a fixed finite motion, one finite stack program computes the exact
deck correction from the varying depth and modular input address in a
polynomial number of bit steps. -/
theorem motionDeck_bit_steps {g : SL} {a : ℕ} (hg : Clears g a) :
    ∃ (u v : Order) (p : Procedure code code (correctionAt a u v (inverseTable a))),
      ∀ (d : ℕ) (hd : 1 ≤ d) (x : Deck (d+2*a)), ∃ n ≤ p.bound.eval (30*(d+2*a+1)),
        Eval p.program
          (single p.input (code ((⟨d⟩,binaryCoords _ (deckAddress _ x).val) : Unary × BinaryCoords)))
          (single p.output (code (binaryCoords d (deckAddress d (motionDeck hg hd x)).val))) n := by
  obtain ⟨u,hu⟩ := hg.1
  obtain ⟨v,hv⟩ := hg.2
  obtain ⟨p⟩ := correctionAt_poly a u v (inverseTable a)
  refine ⟨u,v,p,?_⟩
  intro d hd x
  obtain ⟨n,hn,he⟩ := p.correct (⟨d⟩,binaryCoords _ (deckAddress _ x).val)
  rw [show correctionAt a u v (inverseTable a) (⟨d⟩,binaryCoords _ (deckAddress _ x).val) =
    binaryCoords _ (deckAddress _ (motionDeck hg hd x)).val from
      tableCorrection_exact hg hd u v hu hv x] at he
  exact ⟨n,hn.trans (p.bound.monotone (motionDeck_input_length d a _)),he⟩

end Cover.Frame

end BorderVNP
end Computability
end OAI
