import OAI.Computability.IntegerMultiplication.Wave.Numbers

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Wave
open Param Scale Halo Strip Code Dims Adic Cap Loom Staff Brief Carry Echo Well Moira Bureau
variable {I:Type}(n:I→ℕ)(h:∀i,Season (n i))(a:(i:I)→Direction (n i))
variable {r:Regime I}(T:Origin n r)(A:Realizes r (fun i=>(a i).val))
abbrev symB(i:I):Bits.Word:=
  Bits.short (ν n i) (Cap.coefficient (modulus (n i)) (a i))
include h
theorem symbolV (i:I):
    Bits.value (symB n a i)=Cap.coefficient (modulus (n i)) (a i):=
  Cap.angles_read n (Scale.birthday h) i (a i)
omit h
include T A
theorem symbol : r.Has (symB n a):=
  let p:=Figure.of_spoken A
  (Cap.calibration n T.toCalendar a p).write (T.toCalendar.guide.fund n)
omit T A

-- define little regime. Header constructed globally via r.
abbrev NoteHead:=Bits.Word× Tally ×Bits.Word
abbrev writeP (i:I): NoteHead:=(Bits.short (ν n i+1) (n i),Code.tally (a i).val,symB n a i)
abbrev tablet(i:I):Tree:=send (writeP n a i)
private theorem ok : Dom (Scale.P ∘ n) (fun i=> (tablet n a i).count):= by
  refine ((Dom.const _ 16).mul (Dom.base (Scale.P ∘ n))).mono ?_
  intro i
  have g:0<P (n i):=budget_p _
  have t: (a i).val ≤ P (n i):=
    (a i).isLt.le.trans (Nat.le_self_pow (by decide) _)
  change Code.size (writeP n a i)≤16*(P (n i))
  simp only [writeP,size_prod,size_tally,tally_length,Bits.size_word,Bits.short_length,symB,ν]
  omega
abbrev joltB:Regime I :=
  ⟨Scale.P ∘ n, tablet n a, ok n a⟩
abbrev topic (n:ℕ):=Bits.short (P n+1) n
theorem topic_v(n):Bits.value (topic n)=n:= by
  rw [topic,Bits.value_short]
  have V:= Nat.le_pow_clog (b:=2) (by decide) n
  have h:=Param.four_beta n
  have u:Nat.clog 2 n ≤ beta n:= Nat.le_max_right ..
  exact Nat.mod_eq_of_lt (V.trans_lt ((Nat.pow_lt_pow_iff_right (by decide : 1<(2:ℕ))).mpr (by unfold Scale.P; omega)))
theorem joltH :(joltB n a).Has (writeP n a):= Regime.self
theorem guideQ : Guide (joltB n a) n :=
  ⟨topic ∘ n,(joltH n a).ez Easy.fst,fun _i=>topic_v _⟩
theorem digitQ : Realizes (joltB n a) (fun i=> (a i).val):=(joltH n a).ez Easy.snd.fstCompose
theorem joltQ : (joltB n a).Has (symB n a) :=(joltH n a).ez Easy.snd.sndCompose

include A T
theorem assembly :
    r.Has (writeP n a):=
  (T.guide.amount_.write ((T.guide.fund n).plus (Realizes.fix 1))).pair ((Regime.Has.pair A (symbol n a T A)))

omit T A
include h
-- volume tools. per-prefix budget = side*suffix*P
def Pprice(i:I):ℝ:=
 (ct (A0 n a) i:ℝ) * (ct (Y0 n a true) i:ℝ) * (P (n i):ℝ)
theorem priceP(i:I): 1≤ Pprice n a i:= by
  obtain ⟨_,f,g,_⟩:=atlas n h a true
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by exact_mod_cast f i) (by exact_mod_cast g i)) (by exact_mod_cast budget_p (n i))
theorem costS (i:I): (L0 n a i:ℝ)≤ Pprice n a i:= by
  unfold Pprice ct A0
  rw [Series.count_natural]
  exact (le_mul_of_one_le_right (by positivity) (by exact_mod_cast ((atlas n h a true).p i))).trans
    (le_mul_of_one_le_right (by positivity) (by exact_mod_cast budget_p _))
theorem allot (i:I): ((X0 n a true i).count:ℝ)*Pprice n a i=Bureau.token n i:= by
  unfold Pprice token ton
  have E:=bill0 n a true i
  rw [show Cap.space (criterion (n i))=load _ from (h i).volume] at E
  simp only [← mul_assoc]; norm_cast
  unfold ct at E; rw [E]
theorem per_cost :
    Regime.ripe (r:=joltB n a) (Pprice n a):= by
  refine ⟨priceP n h a,fun k=>?_⟩
  obtain ⟨C,v⟩:= (columnRoof n).2 k
  exact ⟨C,fun i=> (v i).trans (mul_le_mul_of_nonneg_left
    (le_trans (show (Param.room (n i):ℝ) ≤ (L0 n a i:ℝ) by exact_mod_cast (side_le (n i) (a i)).1)
    (costS n h a i)) (Nat.cast_nonneg _))⟩

end Wave

end IntegerMultiplication
end Computability
end OAI
