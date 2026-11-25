import OAI.Computability.IntegerMultiplication.Moira.Cube
import OAI.Computability.IntegerMultiplication.Morse.Alex
import OAI.Computability.IntegerMultiplication.Morse.Catalogue

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Moira
open Bureau Strip Code Param Halo Scale Brief Carry
open Morse Axon Grid Dusk
variable {I:Type}{A:I→Type}
variable (n len wid:I→ℕ)(s:(i:I)→Series (A i))
abbrev midN (i:I):ℕ:= 2^len i
abbrev stepN i := PhaseL (len i)
abbrev tendN i:= Series.natural (wid i)
structure License (n len wid:I→ℕ)(s:(i:I)→Series (A i)):Prop where
  whole i : ct s i * midN len i * wid i=load (n i)
  middle i : len i ≤ Scale.ell (n i)
  small : Figure (city n) (midN len)
  width_ : Figure (city n) wid
variable (v:License n len wid s)
include v
namespace License
-- amen
theorem begun (i):0<ct s i:= by
  by_contra! h
  have e:=v.whole i -- tactic order
  have d:1≤load (n i):= Nat.pow_pos (by decide)
  simp [show ct s i=0 by omega] at e
  omega
-- fix
theorem final_p (i):0<wid i:= by
  have e:=v.whole i
  rcases Nat.eq_zero_or_pos (wid i) with h|h; rw [h,mul_zero] at e; have E : 0<load (n i):=Nat.pow_pos (by decide); omega
  exact h

theorem scope_ :
    Atlas n s (stepN len) (tendN wid) where
  l := v.begun n len wid s
  m i:=by unfold ct stepN; rw [phase_size]; exact Nat.pow_pos (by decide)
  p i:=by rw [ct,tendN, Series.count_natural]; exact v.final_p ..
  total i:=by
    change _ * (PhaseL _).count * (Series.natural _).count≤_
    rw [phase_size,Series.count_natural]
    exact (v.whole i).le.trans (Nat.le_mul_of_pos_right _ (budget_p _))

theorem prefix_ : amen n s := by
  have M : Figure (city n) (fun i=>load (n i)):=
    (Figure.natural 2).repeated ((guide_city n).exSize n)
  have e:= M.quotients (v.small.multiplied v.width_)
  have u (i:I): load (n i)/(midN len i * wid i)=ct s i := by
    rw [← v.whole i,Nat.mul_assoc]
    exact Nat.mul_div_cancel _ (Nat.mul_pos (Nat.pow_pos (by decide)) (v.final_p ..))
  simp only [u] at e; exact e
end License
variable (x:(i:I)→A i→ Morse.Deck (len i) (wid i) (Scale.W (n i)))(b:(i:I)→ℕ→Grain (Scale.W (n i))) (q:I→ Bits.Word)
abbrev scriptv (i:I) (a:A i)(j:Face (len i))(c:Fin (wid i)):Code.Tree:=send (Dusk.mark (x i a j c))
theorem start :
    close n (raw s (stepN len) (tendN wid) (scriptv n len wid x)) := by
  apply wide s (stepN len) (tendN wid) 40000
  · intro i; rw [ct,ct,ct,stepN,tendN,phase_size,Series.count_natural]
    exact (v.whole i).le
  intro i a j k
  change Code.size (Dusk.mark _)≤_
  rw [Dusk.volume]; have e:= near_ (n i); have p:1≤P (n i):=budget_p _; omega

-- raw grouped triple= rows
abbrev prim (i:I)(a:A i):=Morse.card (x i a)
omit v
theorem align :
    triple s (stepN len) (tendN wid) (scriptv n len wid x) = stackRun s (fun i a=> send (prim n len wid x i a)) := by
  unfold triple stackRun
  funext i; apply congrArg (stripe _); funext a
  change stripe (PhaseL _) (fun j=>stripe (Series.natural _) (fun c=>send (Dusk.mark (x i a j c))))=_
  have d(k)(f:Fin k→Dusk.Pair): Series.tab (Series.natural k) f=List.ofFn f:=by
    change List.map _ (List.finRange _)=_
    simp [List.finRange,Function.comp_def]
  simp_rw [stripe_eq',d]
  rfl
include v
-- initial packet + geometry grouping
abbrev dust := raw s (stepN len) (tendN wid) (scriptv n len wid x)
theorem primed :
    Wood n (dust n len wid s x) (stackRun s (fun i a=>send (prim n len wid x i a))) := by
  rw [← align]
  have M:amen n (stepN len):=by unfold amen ct stepN; simp_rw [phase_size]; exact v.small
  have P:amen n (tendN wid):=by unfold amen ct tendN; simp_rw [Series.count_natural]; exact v.width_
  exact authorize s _ _ _ (me (start n len wid s v x)) (v.prefix_ ..) M P (v.scope_ ..)
end Moira

end IntegerMultiplication
end Computability
end OAI
