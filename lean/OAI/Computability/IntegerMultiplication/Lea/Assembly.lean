import OAI.Computability.IntegerMultiplication.Lea.Output
import OAI.Computability.IntegerMultiplication.Brief.Launch

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Lea
open Param Scale Code Strip Bureau Cap Echo Dusk Cone Brief Dune Staff Carry Bits
variable {I:Type} (n:I→ℕ)(h:∀i,Season (n i))(x y:I→Word)
variable (p:∀i,(x i).length=n i)(q:∀i,(y i).length=n i)

abbrev answer (j: Interface.Pair): Bits.Word:=
  (sized (2*j.1.length) (Bits.product (j.1.reverse,j.2.reverse))).reverse
theorem date_length (j): (answer j).length=2*j.1.length:= by unfold answer; simp
private theorem value_ans {j:Interface.Pair}(v:j.1.length=j.2.length):
    bitValue j.1 * bitValue j.2 < 2^(2*j.1.length):= by
  have V:= value_lt j.1.reverse; have H:= value_lt j.2.reverse
  rw [endianness,endianness,two_mul,pow_add]
  rw [List.length_reverse] at V H
  rw [← v] at H
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ V.le) (Nat.mul_lt_mul_of_pos_left H (Nat.pow_pos (by decide)))
theorem value_answer {j:Interface.Pair}(v:j.1.length=j.2.length):
    bitValue (answer j)=bitValue j.1*bitValue j.2 := by
  unfold answer
  rw [endianness,List.reverse_reverse,sized_low,exact_prod]
  change (value j.1.reverse*value j.2.reverse)%_=_
  rw [← endianness,← endianness,Nat.mod_eq_of_lt (value_ans v)]

abbrev inputs(i:I):Interface.Pair:=(x i,y i)
noncomputable section
-- specialized large all proxies
variable (z:Faculty n)(u : z.release n (city n))(H:z.quality n)
abbrev output_ (i:I):GrainV (n i):=
  curtainR n h z (water n x) (water n y) i
include H h p q
theorem enables (i:I)(j:Hint (n i)):
    value (ear n (output_ n h x y z) i j)=
      Cap.tally (s:=modulus (n i)) (lot n x i) (lot n y i) j :=
  gleaned n _ _ _ _ (Dune.finishes n h z H (water n x) (water n y)
    (lot n x) (lot n y)
    (fun i j=> portrays (n i) _ (lotP n x i j))
    (fun i j=> portrays (n i) _ (lotP n y i j))
    (fun _i=>Cone.lookingZero _)
    (fun i j=>(lotP n x i j).le) (fun i j=>(lotP n y i j).le)
    (sparseR n h x p) (sparseR n h y q) i j)
theorem engage (i:I) :
    emit n (output_ n h x y z) i = answer (inputs x y i) := by
  let a:=output_ n h x y z; let j:=inputs x y i; let t:=n i
  have v:j.1.length=j.2.length:= (p i).trans (q i).symm
  apply List.reverse_injective
  unfold emit
  rw [List.reverse_reverse]
  apply word_inject
  · rw [sized_length,List.length_reverse,date_length]
    rw [show (inputs x y i).1.length=n i from p i]
  rw [sized_low,← endianness, savored (P (n i)) _ (ear n _ i) (layer_ok n _ i)]
  have W : (value ∘ ear n a i)=Cap.tally (s:=modulus t) (lot n x i) (lot n y i) := funext fun j=> enables n h x y p q z H i j
  change Cap.score (radix (P t)) (value ∘ ear n a i)%_=_
  rw [W, scoreboard _ _ _ (Param.amount t) (sparseR n h x p i) (sparseR n h y q i) (h i).enoughBits,scoreR n h x p,scoreR n h y q]
  change (bitValue j.1 * bitValue j.2)%_=bitValue (answer j)
  rw [value_answer v,show n i=j.1.length from (p i).symm,Nat.mod_eq_of_lt (value_ans v)] -- t
omit H
abbrev words :=send ∘ inputs x y
abbrev goalB (n:ℕ):ℝ:= (n:ℝ)*Param.reward n
theorem large_ :
    Carries (goalB ∘ n) (words x y) (fun i=>send (answer (inputs x y i))) := by
  obtain ⟨z,H,u⟩:= Faculty.obtain_ n (Scale.birthday h)
  let s i:=send (x i); let t i:=send (y i)
  let g:=together s t
  have U:= sizeInput n x p
  have V:= sizeInput n y q
  have W:= me (U.fork V (chargep n))
  change Wood n g g at W
  have T := (combine (W.chain (Carries.dropRight (chargep n) U V)) (loomso n h x p)).twice
    (combine (W.chain (Carries.dropLeft (chargep n) U V)) (loomso n h y q))
  have Q:= Dune.shuttle n h Phase.order_ (Series.arbitrary _) z u (water n x) (water n y)
  have R:= transport (transport (inherit T (color_p n)) Q) (inherit (leaf n h (output_ n h x y z)) (color_p n))
  simp_rw [engage n h x y p q z H] at R
  have Y:=Brief.launch x y p q
  let f:=goalB ∘ n
  have P0 (i:I) : 1≤ reward (n i):= Real.one_le_rpow (by exact_mod_cast (show 1≤beta _ from Nat.le_max_left ..))
    (by norm_num)
  have P1(i:I): 1≤ (n i:ℝ):=by exact_mod_cast ((h i).large)
  have P2(i:I): (n i:ℝ)≤ f i := le_mul_of_one_le_right (by positivity) (P0 i)
  have P3(i:I): 1≤f i := (P1 i).trans (P2 i)
  have E : Carries f (words x y) (together (cell n) g) := Y.times P3 2 (fun i=>by
    unfold Brief.measure; push_cast; linarith [P3 i,P2 i])
  refine E.chain (R.times P3 (32*2^(36:ℕ)) (fun i=>?_))
  have m : token n i ≤ 32*(n i:ℝ):= by
    unfold token ton; exact_mod_cast (by rw [Nat.mul_comm (load _)]; exact (h i).wide : load (n i)*P (n i) ≤ _)
  have k := fund_gate (n i)
  apply le_trans (mul_le_mul m k (by linarith [fund1 (n i)]) (by positivity))
  unfold f goalB Function.comp; push_cast; ring_nf; exact le_rfl
end
end Lea

end IntegerMultiplication
end Computability
end OAI
