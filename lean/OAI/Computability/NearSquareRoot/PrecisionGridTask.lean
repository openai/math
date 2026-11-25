import OAI.Computability.IntegerMultiplication.Grid.Bond
import OAI.Computability.NearSquareRoot.ShortWord
import OAI.Computability.NearSquareRoot.ShortWordCall
import OAI.Computability.NearSquareRoot.PrecisionGrid
import OAI.Computability.IntegerMultiplication.Code.Padding

/-! # Tape cost of signed complex fixed-point multiplication

The physical short-word multiplier takes positive equal-width MSF inputs.
The P192 grid routines use LSF sign-and-magnitude words. Include the
padding, reversal, redundant output digits, sign handling and fixed-point
shifts in the cost of the record operation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GridTask
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits

/-- Quasilinear tape allowance for a record containing `w` symbols. -/
def recordCost (w : ℕ) := (w + 1) * (Nat.clog 2 (w + 1) + 1)

private def sumRuler (x : Toom.IW) := ruler x.1 ++ ruler x.2

private def padded (x : Toom.IW) : Toom.IW :=
  let t := () :: sumRuler x
  ((resize (t, x.1)).reverse, (resize (t, x.2)).reverse)

private def finish (x : Word × Tally) : Word := resize (x.2 ++ x.2, x.1.reverse)

private theorem setup_easy : Easy (fun x : Toom.IW => (padded x, sumRuler x)) := by
  unfold padded sumRuler
  fun_prop

private theorem finish_easy : Easy finish := by unfold finish; fun_prop

private theorem padded_eq (x : Toom.IW) :
    let n := x.1.length + x.2.length + 1
    padded x = ((sized n x.1).reverse, (sized n x.2).reverse) := by
  have h := recover_tally (() :: sumRuler x)
  simp only [List.length_cons, sumRuler, List.length_append, ruler_length] at h
  simp only [padded, sized, h, sumRuler]

private theorem pad_length (x : Toom.IW) :
    (padded x).1.length = x.1.length + x.2.length + 1 ∧
    (padded x).2.length = x.1.length + x.2.length + 1 := by
  simp [padded_eq]

private theorem pad_value (x : Toom.IW) :
    bitValue (padded x).1 = value x.1 ∧ bitValue (padded x).2 = value x.2 := by
  have trim (a : Word) {n : ℕ} (h : a.length ≤ n) :
      value (sized n a) = value a := by
    rw [sized_low, Nat.mod_eq_of_lt ((value_lt a).trans_le (Nat.pow_le_pow_right (by decide) h))]
  simp only [padded_eq, endianness, List.reverse_reverse]
  exact ⟨trim _ (by omega), trim _ (by omega)⟩

private theorem finish_eq (x : Toom.IW) (z : Word)
    (h : bitValue z = value x.1 * value x.2) :
    finish (z, sumRuler x) = Bits.product x := by
  let w := 2 * (x.1.length + x.2.length)
  have e : tally w = sumRuler x ++ sumRuler x := by
    convert recover_tally (sumRuler x ++ sumRuler x) using 1
    simp [sumRuler, w, two_mul, Nat.add_assoc]
  change resize (sumRuler x ++ sumRuler x, z.reverse) = _
  rw [← e]
  change sized w z.reverse = _
  apply word_inject
  · rw [sized_length, length_prod]
  · have hw : value (Bits.product x) < 2 ^ w := by
      simpa [w, length_prod] using value_lt (Bits.product x)
    rw [sized_low, ← endianness, h, ← exact_prod, Nat.mod_eq_of_lt hw]

/-- Adapt a word multiplier on the padded MSF inputs to the exact redundant
LSF output used by the signed-record routines. This includes zero-width words. -/
private theorem adapt (reply : Toom.IW → Word)
    (run : Task (fun x : Toom.IW => (padded x).1.length *
        max 1 (Nat.clog 2 (padded x).1.length))
      (fun x => send (padded x)) (fun x => send (reply x)))
    (hlen : ∀ x, (reply x).length = 2 * (padded x).1.length)
    (hval : ∀ x, bitValue (reply x) = bitValue (padded x).1 * bitValue (padded x).2) :
    Computes (fun x => recordCost (size x)) Bits.product := by
  have call := run.left (fun x => send (sumRuler x))
  have post := Task.on finish_easy (fun x => (reply x, sumRuler x))
  have result := (Task.compose (Task.compose setup_easy call) post)
  have he (x : Toom.IW) : finish (reply x, sumRuler x) = Bits.product x :=
    finish_eq _ _ (by rw [hval, (pad_value x).1, (pad_value x).2])
  simp only [he] at result
  apply result.bound 20
  intro x
  have hsize : x.1.length + x.2.length + 1 ≤ size x + 1 := by
    rw [size_prod, size_word, size_word]; omega
  have hh : max 1 (Nat.clog 2 (x.1.length + x.2.length + 1)) ≤
      Nat.clog 2 (size x + 1) + 1 :=
    max_le (by omega) (Nat.le_succ_of_le (Nat.clog_monotone _ hsize))
  have hcost := Nat.mul_le_mul hsize hh
  have hs : size x + 1 ≤ recordCost (size x) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  simp only [size_prod, size_word, size_tally, hlen, (pad_length x).1, sumRuler,
    List.length_append, ruler_length]
  unfold recordCost at hs ⊢
  simp only [size_prod, size_word] at hs hcost hsize
  omega

/-- A scan of a whole record fits in the multiplication clock. -/
theorem width_le_recordCost (w : ℕ) : w + 1 ≤ recordCost w :=
  Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

/-- A constant-factor change of record width costs a constant-factor change in time. -/
theorem recordCost_scale (C : ℕ) :
    ∃ D : ℕ, ∀ w s : ℕ, s ≤ C * (w + 1) → recordCost s ≤ D * recordCost w := by
  refine ⟨(C + 1) * (Nat.clog 2 (C + 1) + 1), fun w s h => ?_⟩
  have hlen : s + 1 ≤ (C + 1) * (w + 1) := by rw [Nat.add_mul]; omega
  have hlog : Nat.clog 2 (s + 1) ≤ Nat.clog 2 (C + 1) + Nat.clog 2 (w + 1) := by
    rw [Nat.clog_le_iff_le_pow (by decide), pow_add]
    exact hlen.trans (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _)
      (Nat.le_pow_clog (by decide) _))
  have hb : Nat.clog 2 (s + 1) + 1 ≤ (Nat.clog 2 (C + 1) + 1) *
      (Nat.clog 2 (w + 1) + 1) := by
    rw [Nat.add_mul, Nat.mul_add]; omega
  simpa only [recordCost, Nat.mul_mul_mul_comm] using Nat.mul_le_mul hlen hb

/-- The output has linear encoded length; a call costs O(w log(2+w)).
The length invariant permits arbitrary fixed compositions of the record operations. -/
@[fun_prop] private structure Fast {A B : Type} [Codec A] [Codec B] (f : A → B) : Prop where
  length : ∃ C : ℕ, ∀ a, size (f a) ≤ C * (size a + 1)
  run : Computes (fun a => recordCost (size a)) f

private theorem fromEasy {A B : Type} [Codec A] [Codec B] {f : A → B}
    (h : Easy f) : Fast f := by
  obtain ⟨c, hc⟩ := h.length
  exact ⟨⟨c, fun x => (hc x).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))⟩,
    h.mono (fun x => (Nat.le_succ _).trans (width_le_recordCost _))⟩

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

@[fun_prop] private theorem fastId : Fast (fun x : A => x) := fromEasy Easy.identity

@[fun_prop] private theorem fastCompose {f : A → B} {g : B → C}
    (p : Fast f) (q : Fast g) : Fast (fun x => g (f x)) := by
  obtain ⟨b, hb⟩ := p.length
  obtain ⟨c, hc⟩ := q.length
  obtain ⟨d, hd⟩ := recordCost_scale b
  constructor
  · refine ⟨c * (b + 1), fun x => ?_⟩
    apply (hc _).trans
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [Nat.add_mul]
    have := hb x
    omega
  · apply (Computes.comp q.run p.run).bound (d + 1)
    intro x
    have h := hd (size x) _ (hb x)
    rw [Nat.add_mul, Nat.mul_add]
    omega

@[fun_prop] private theorem fastFst {f : A → B × C} (p : Fast f) :
    Fast (fun x => (f x).1) := fastCompose p (fromEasy Easy.fst)

@[fun_prop] private theorem fastSnd {f : A → B × C} (p : Fast f) :
    Fast (fun x => (f x).2) := fastCompose p (fromEasy Easy.snd)

@[fun_prop] private theorem fastPair {f : A → B} {g : A → C}
    (p : Fast f) (q : Fast g) : Fast (fun x => (f x, g x)) := by
  obtain ⟨b, hb⟩ := p.length
  obtain ⟨c, hc⟩ := q.length
  constructor
  · refine ⟨b + c + 1, fun x => ?_⟩
    rw [size_prod, Nat.add_mul, Nat.add_mul]
    change size (f x) + size (g x) + 1 ≤ _
    have := hb x
    have := hc x
    omega
  · have h := ((Task.copy (send (X := A))).compose (p.run.left send)).compose
      (q.run.right (fun x => send (f x)))
    apply h.bound (b + 4)
    intro x
    change size x + recordCost (size x) + (size (f x) + recordCost (size x)) + 1 ≤ _
    have hf := (hb x).trans (Nat.mul_le_mul_left b (width_le_recordCost (size x)))
    have hx := width_le_recordCost (size x)
    rw [Nat.add_mul, Nat.mul_add]
    omega

private def domain (x : Toom.IW) : Domain :=
  ⟨⟨padded x, (pad_length x).1.trans (pad_length x).2.symm⟩, by
    change 1 ≤ (padded x).1.length
    rw [(pad_length x).1]; omega⟩

/-- The full redundant LSF word used by P192, obtained by invoking its faster
equal-length multiplier under a return frame. -/
theorem wordProduct : Computes (fun x => recordCost (size x)) Bits.product := by
  apply adapt (fun x => Lea.answer (padded x)) (ShortWord.productTask.on domain)
  · exact fun x => (ShortWord.productSpec (domain x)).1
  · exact fun x => (ShortWord.productSpec (domain x)).2

private theorem fastWordProduct : Fast Bits.product := by
  refine ⟨⟨4, fun x => ?_⟩, wordProduct⟩
  rw [size_prod, size_word, length_prod, size_word, size_word]
  omega

private theorem fastSigned : Fast Grid.prod := by
  unfold Grid.prod
  have s := fromEasy (Easy.finite Grid.signX)
  have m := fastWordProduct
  fun_prop

private theorem fastComplex : Fast Grid.timesG := by
  unfold Grid.timesG
  have p := fastSigned
  have a := fromEasy Grid.easy_plus
  have b := fromEasy Grid.easy_neg
  fun_prop

private theorem fastAdjust : Fast Grid.adjust := by
  have w : Fast (fun x : Dusk.Pair × Grid.Orb => ruler x.1.1) := fromEasy (by fun_prop)
  have s := fromEasy Grid.spell_easy
  have f := fromEasy Grid.fit_easy
  have r := fromEasy Grid.rest_easy
  have d := fromEasy Grid.disp_easy
  have p := fastComplex
  unfold Grid.adjust
  fun_prop

/-- All four signed products and both fractional shifts operate on the record
itself. Parked stack data are restored by every call. -/
theorem adjustTask : Computes (fun x => recordCost (size x)) Grid.adjust := fastAdjust.run

/-- Mapping the command over a whole record stream charges all calls and a
linear pass over the stream. -/
theorem adjustStream : Computes
    (fun l => size l + costSum (fun x => recordCost (size x)) l) (List.map Grid.adjust) :=
  adjustTask.mapping

/-- A stream of at most `N` width-`w` records runs within one
`O(N(w+1)(1+clog₂(w+1)))` allowance, with all list traversals charged. -/
theorem adjustStreamBounded {I : Type} (N w : I → ℕ)
    (l : I → List (Dusk.Pair × Grid.Orb)) (C : ℕ)
    (hn : ∀ i, (l i).length ≤ N i) (hw : ∀ i, ∀ z ∈ l i, size z ≤ C * (w i + 1)) :
    Task (fun i => N i * recordCost (w i))
      (fun i => send (l i)) (fun i => send ((l i).map Grid.adjust)) := by
  obtain ⟨d, hd⟩ := recordCost_scale C
  apply (adjustStream.on l).bound (C + d + 3)
  intro i
  have hsum (f : Dusk.Pair × Grid.Orb → ℕ) (b : ℕ)
      (h : ∀ z ∈ l i, f z ≤ b) : costSum f (l i) ≤ N i * b := by
    have u := costSum_le (u := fun _ => b) h
    simpa [costSum, Nat.mul_comm] using
      u.trans (show costSum (fun _ => b) (l i) ≤ N i * b by
        simpa [costSum, Nat.mul_comm] using Nat.mul_le_mul_right b (hn i))
  have a := hsum size _ (hw i)
  have b := hsum (fun z => recordCost (size z)) _
    (fun z hz => hd (w i) (size z) (hw i z hz))
  have t := width_le_recordCost (w i)
  have x : N i * (C * (w i + 1)) ≤ C * (N i * recordCost (w i)) := by
    rw [Nat.mul_left_comm]; gcongr
  have y : N i ≤ N i * recordCost (w i) := Nat.le_mul_of_pos_right _ (by omega)
  have z := costSum_le_length_size (l i)
  have n := hn i
  rw [Nat.mul_left_comm (N i) d] at b
  simp only [Nat.add_mul, Nat.mul_add] at *
  omega

/-- The physical encoding of the rounded product on a family of `w+1`-bit
grid words. Local operands and the precision ruler have ordinary tape cost. -/
theorem launchTask {I : Type} (w : I → ℕ) (f : I → Grid.Orb)
    (x : (i : I) → Dusk.Grain (w i)) (C : ℕ) (hf : ∀ i, size (f i) ≤ C * (w i + 1)) :
    Task (fun i => recordCost (w i))
      (fun i => send (Dusk.mark (x i), f i))
      (fun i => send (Dusk.mark (Grid.launch (x i, f i)))) := by
  have h := adjustTask.on (fun i => (Dusk.mark (x i), f i))
  simp only [Grid.inject] at h
  obtain ⟨d, hd⟩ := recordCost_scale (8 + C)
  apply h.bound (d + 1)
  intro i
  have hs : size (Dusk.mark (x i), f i) ≤ (8 + C) * (w i + 1) := by
    rw [size_prod, Dusk.volume, Nat.add_mul]
    change 4 * (w i + 1) + 3 + size (f i) + 1 ≤ _
    have := hf i
    omega
  have hc := hd (w i) _ hs
  rw [Nat.add_mul, Nat.mul_add]
  omega

/-- One fixed compiled subroutine for all array widths in the precision proof.
The caller supplies both marked complex records and the unary fractional ruler.
The multiplier rewinds the scratch tapes upon return. -/
theorem physicalMultiply {I : Type} (k : I → ℕ)
    (x y : (i : I) → FixedPoint.Record (k i)) :
    ShortWord.PhysicalTask (fun i => recordCost (k i))
      (fun i => send (Dusk.mark (x i), tally (FixedPoint.fractionBits (k i)), Dusk.mark (y i)))
      (fun i => send (Dusk.mark (FixedPoint.multiply (k i) (x i) (y i)))) := by
  apply ShortWord.physicalTask
  let w (i : I) := FixedPoint.componentBits (k i)
  let f (i : I) : Grid.Orb := (tally (FixedPoint.fractionBits (k i)), Dusk.mark (y i))
  have hf (i : I) : size (f i) ≤ 10 * (w i + 1) := by
    change size (tally (FixedPoint.fractionBits (k i))) + size (Dusk.mark (y i)) + 1 ≤
      10 * (FixedPoint.componentBits (k i) + 1)
    rw [size_tally, tally_length, Dusk.volume, FixedPoint.fractionBits, FixedPoint.componentBits]
    omega
  have task := launchTask w f x 10 hf
  obtain ⟨d, hd⟩ := recordCost_scale 100
  apply task.bound (d + 1)
  intro i
  have z : w i ≤ 100 * (k i + 1) := by unfold w FixedPoint.componentBits; omega
  have := hd (k i) _ z
  rw [Nat.add_mul, Nat.mul_add]
  omega

end GridTask

end NearSquareRoot
end Computability
end OAI
