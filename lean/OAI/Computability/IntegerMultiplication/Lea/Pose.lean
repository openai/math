import OAI.Computability.IntegerMultiplication.Lea.Crops

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Lea
open Code Bits Dusk Grid Cone Halo Param Scale
-- wire radix value to gaussian grid
variable (n:ℕ)
abbrev raw (b:ℕ):Grid.Cell:=⟨(b*(2^Scale.F n):ℕ),0⟩
def fluid (b:ℕ) : G n:= Grid.wrapMap (W n) (raw n b)
theorem counts (b:ℕ)(v:b<2^P n) : b*2^Scale.F n<2^W n:= by
  have P: P n+Scale.F n≤W n:=by unfold Scale.F Scale.W; omega
  exact (Nat.mul_lt_mul_of_pos_right v (Nat.pow_pos (by decide))).trans_le (by rw [← pow_add]; gcongr)
theorem portrays (b:ℕ)(q:b<2^P n):
    look n (fluid n b)=(b:ℂ):= by
  have t: Grid.focus (W n) (raw n b):= by
    unfold Grid.focus Grid.tiny
    simp only [Int.abs_natCast]
    exact ⟨by exact_mod_cast counts n b q,by rw [abs_zero]; exact pow_pos (by norm_num) _⟩
  unfold look meaning fluid
  rw [Grid.recovers _ t]
  suffices e : toC (raw n b)=(b:ℂ)*2^Scale.F n by rw [e,mul_div_cancel_right₀ _ (pow_ne_zero _ (by norm_num))]
  simp [toC,raw]
  -- simp int nat cast?
-- wire data from crop p and fractional command (fixed W=2*factor)
def pedal (x:Word ×Tally) : Dusk.Pair :=
  let f:=fill false x.2
  let w:=()::x.2++x.2
  (Bits.resize (w, f++x.1), fill false w)
@[fun_prop] theorem pedalE: Easy pedal:=by unfold pedal; fun_prop
theorem runs {x:Word}(v:value x<2^P n):
    pedal (x,Code.tally (Scale.F n))= Dusk.mark (fluid n (value x)):= by
  let W:=Scale.W n
  let p:=Scale.F n
  have H:W=p+p:=by unfold W Scale.W p Scale.F; omega
  let s:=Code.tally p
  let t:=()::s++s
  have L:t=Code.tally (W+1):= by rw [← recover_tally t]; unfold t s; simp [H,Nat.add_right_comm]
  have E : (2:ℕ)^W≤ Dusk.period W := by have e:= period_s W; rw [pow_succ] at e; have h:0<(2:ℕ)^W:=Nat.pow_pos (by decide); omega
  have M : value x * 2^p < Dusk.period W:= (counts n _ v).trans_le E
  have A : ZMod.val (fluid n (value x)).re=value x*2^p:= by
    change ZMod.val ((↑((↑(value x*2^p:ℕ)):ℤ)):day W)=_
    simp only [Int.cast_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt M]
  apply Prod.ext
  · change resize (t,fill false s ++ x)=trip _
    apply word_inject
    · rw [L,trip_length]; exact sized_length ..
    · rw [L]; change value (sized (W+1) _)=_
      rw [sized_low,value_append,fill_eq,tally_length,zeroes,List.length_replicate,zero_add,trips,A,mul_comm]
      exact Nat.mod_eq_of_lt (by have g:= counts n _ v; exact g.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
  change fill false t=trip _
  apply word_inject
  · rw [trip_length,L,fill_eq,tally_length,List.length_replicate]
  rw [fill_eq,zeroes,trips,show (fluid n (value x)).im=0 from (by simp [fluid, wrapMap, raw]),ZMod.val_zero]

end Lea

end IntegerMultiplication
end Computability
end OAI
