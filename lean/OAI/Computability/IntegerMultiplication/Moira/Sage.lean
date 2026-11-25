import OAI.Computability.IntegerMultiplication.Moira.Sheet

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Moira
open Bureau Strip Code Param Halo Scale Brief Carry
open Morse Axon Grid Dusk
variable {I:Type}{A:I→Type}
variable (n len wid:I→ℕ)(s:(i:I)→Series (A i))(v:License n len wid s)
variable (x:(i:I)→A i→ Morse.Deck (len i) (wid i) (Scale.W (n i)))
variable (b:(i:I)→ℕ→Grain (Scale.W (n i))) (q:I→Bits.Word)
theorem rim (n:ℕ): Scale.F n≤Scale.W n+1:=by unfold Scale.F Scale.W; omega
abbrev pub (i:I):=Morse.scroll (Scale.F (n i)) (q i) (b i) (len i)
theorem price_ (i:I):
    size (pub n len b q i)≤ (32*8193)*P (n i)*midN len i :=
  le_trans (grace _ _ _ (rim (n i)) (len i)) (by
    unfold midN; have e:= Nat.mul_le_mul_left (32*2^len i) (near_ (n i)); nlinarith)
variable (g:(city n).Has (pub n len b q))
include v g
variable {u:I→Tree}
theorem authorized (p:close n u):
    Wood n u (stackRun s fun i _=>send (pub n len b q i)) := by
  have a:= v.scope_ n len wid s
  have v0:= (scoop p).chain (dispatchT _ (v.prefix_ ..) a.pair.first)
  have v1:= rescue p g
  apply Strip.spread s _ (v0.twice v1)
  refine ⟨32*8193*2,fun i=>?_⟩
  change _*(size _:ℝ)≤ _*_
  unfold token ton
  have E: ((s i).count+1)*size (pub n len b q i)≤ (32*8193*2)*(load (n i)*P (n i)) := calc
   _ ≤ (2*(s i).count)* ((32*8193)*P (n i)*(midN len i)) :=
    Nat.mul_le_mul (by have t:=v.begun n len wid s i; unfold ct at t; omega) (price_ n len b q i)
   _ ≤ _:= by
    have M := (Nat.le_mul_of_pos_right ((s i).count*midN len i) (v.final_p n len wid s i)).trans (v.whole i).le
    calc
      _ = ((32*8193*2)*((s i).count*midN len i))*P (n i):=by ring
      _ ≤ _ := by rw [Nat.mul_assoc ((32:ℕ)*8193*2) _ (P (n i))]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ M)
  exact_mod_cast E

noncomputable section
abbrev BOM (i:I)(a:A i):Morse.Order :=
  ⟨len i,wid i,Scale.W (n i),Scale.F (n i),q i,b i,x i a,rim _⟩
abbrev certn (i:I)(a:A i):=study (BOM n len wid x b q i a) (x i a)

omit g in
theorem taxWave :
    ∃ C:ℕ,∀ i, (s i).count*((len i+1:ℝ)*((2^len i*(wid i+1)*(Scale.W (n i)+1)*Grid.tax (Scale.W (n i)):ℕ):ℝ))+1 ≤ C*grant n (Bureau.hue n) i := by
  obtain ⟨k,H⟩:= Param.taxFund 8192
  refine ⟨8193*2*k+1,fun i=>?_⟩
  let t:=n i
  have e:= v.final_p n len wid s i
  have Z : (s i).count*(2^len i)*(wid i+1)*(Scale.W t+1) ≤ 8193*2*ton n i := by
    have U:(s i).count*2^len i*(wid i)=load t:=v.whole i
    calc
      _ ≤ (s i).count*2^len i*(2*wid i)*(8193*P t) := by gcongr <;> first|omega| exact near_ t
      _ = _:=by unfold ton; nlinarith [U] -- multiply U by P explicitly
  have ca : (Grid.tax (Scale.W t):ℝ)*((span_ t:ℝ)+1)≤ (k:ℝ)*hue n i:=
    H t (Scale.W t) (by unfold Scale.W P; omega)
  have q0:(len i:ℝ)≤ span_ t:= by exact_mod_cast v.middle i
  have M := ca.trans' (mul_le_mul_of_nonneg_left (add_le_add_left q0 1) (Nat.cast_nonneg (Grid.tax (Scale.W t))))
  let V:=((s i).count:ℝ)
  have N : V*2^len i*(wid i+1)*(Scale.W t+1)≤8193*2*token n i:=by unfold V token; exact_mod_cast Z
  change V*_+1≤_
  push_cast
  let B:= Grid.tax (Scale.W t)
  change V*((len i+1:ℝ)*(2^len i*(wid i+1)*(Scale.W t+1)*↑B))+1≤_
  have T : 0 ≤ (8193:ℝ)*2*token n i:=by unfold token; positivity
  have Q:= mint_ n (color_p n) i
  have L : V*2^len i*(wid i+1)*(Scale.W t+1)* (B * (len i+1):ℝ)≤
      8193*2*token n i*(k*hue n i):= mul_le_mul N (by simpa only [add_comm (1:ℝ) (len i:ℝ)] using M) (by positivity) T
  unfold grant at *; nlinarith

include g
set_option maxHeartbeats 500000 in
/-- Full release one FFT axis on flat grammar.  Factors and precision p provided in the Scroll via header, for all ghost payloads uniformly. -/
theorem saga :
    Spun n (hue n) (dust n len wid s x) (dust n len wid s (certn n len wid x b q)) := by
  let Y:= certn n len wid x b q
  apply IntegerMultiplication.Moira.conform s (stepN len) (tendN wid) (scriptv n len wid Y)
  rw [align]
  have W:=primed n len wid s v x
  have t:=authorized n len wid s v b q g (Volume.right W.small)
  let r(i:I)(a:A i):=BOM n len wid x b q i a
  have T : Wood n (dust n len wid s x) (stackRun s fun i a=>ready (r i a)) := by
    exact Strip.coalesce s _ _ t W
  let d (i:I):ℝ:= (len i+1:ℝ)*((2^len i*(wid i+1)*(Scale.W (n i)+1)*Grid.tax (Scale.W (n i)):ℕ):ℝ)
  have L:=liftoff s (fun i a=> ready (r i a)) (fun i a=>react (r i a)) d
    (Morse.money.slide (fun j:Sigma A=>r j.1 j.2))
  obtain ⟨c,P⟩:= taxWave n len wid s v
  exact (inherit T (color_p n)).chain (L.times (mint_ n (color_p n)) c P)
end
end Moira

end IntegerMultiplication
end Computability
end OAI
