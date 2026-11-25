import OAI.Computability.IntegerMultiplication.Star.Music

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Star
open Code Brief Grid Carry Staff Strip Dusk
variable {J:Type} {r:Regime J}
private theorem court (x:J→ℝ) (h:Blot r x) :
    ∃ t:J→S, r.Has t ∧ ∀ i, |(Grid.whole (t i):ℝ)-x i| ≤ 1 := by
  obtain ⟨a,p,v,y⟩:=h.ticket
  -- use truncate theorem
  refine ⟨_,p.thenDo Brief.quotientP,fun i=>?_⟩
  rw [← y]
  change |(Grid.whole (Brief.sq (a i)):ℝ)-_/_|≤1
  obtain e : a i=((a i).1,(a i).2):= rfl
  exact Brief.sq_close _ _ (v i)
theorem film (x:J→ℂ) (h:Curve r x) (n:J→ℕ) (p:Realizes r n) :
    ∃ z:J→ Grid.Coef,r.Has z ∧ ∀ i, ‖Grid.toC (Grid.content (z i)) - x i*2^n i‖ ≤ 2 := by
  have q : Curve r (fun i=>(2:ℂ)^n i) := by
    have T : Curve r (fun i=>((↑(((2:ℕ)^n i:ℕ):ℝ)):ℂ)) :=
      Curve.real (Blot.natural ((Figure.natural 2).repeated p))
    push_cast at T; exact T
  obtain ⟨A,P⟩:=h.mul q
  obtain ⟨t,g,v⟩:=court _ A
  obtain ⟨s,u,e⟩:=court _ P
  refine ⟨_,g.pair u,fun i=>?_⟩
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  specialize v i; specialize e i
  rw [Complex.sub_re,Complex.sub_im]
  have a (x:Cell) : (toC x).re=(x.re:ℝ) ∧ (toC x).im=(x.im:ℝ) := by simp [toC]
  rw [(a _).1,(a _).2]
  change |((whole (t i)):ℝ)-_|+|((whole (s i)):ℝ)-_|≤ 2
  exact add_le_add v e |>.trans (by norm_num)
variable (x:J→ℂ) (n k:J→ℕ)
variable (p:Realizes r n) (w: Realizes r k)
abbrev Satisfactory (r:Regime J) (f:(i:J)→Grain (k i)) := r.Has (fun i=>Dusk.mark (f i))
include p w
theorem stroke (h:Curve r x) (v:∀ i, ‖x i‖*2^n i + 2 < 2^k i):
    ∃ b : (i:J)→Grain (k i), Satisfactory k r b ∧
      ∀ i, ‖meaning (n i) (k i) (b i) - x i‖ ≤ 2*drop_ (n i) := by
  obtain ⟨f,t,e⟩:=film _ h _ p
  have H i :
      ‖toC (content (f i))‖ < 2^k i := by
    have u := norm_add_le (toC (content (f i)) - x i*2^n i) (x i*2^n i)
    rw [sub_add_cancel,norm_mul,norm_pow,show ‖(2:ℂ)‖=(2:ℝ) by norm_num] at u
    exact u.trans_lt (by linarith [e i,v i])
  have p i := Grid.short _ (Grid.into _) (H i)
  let q (i:J):Grain (k i):=wrapMap (k i) (content (f i))
  have g i : focus (k i+1) (content (f i)) := by
    specialize p i
    have T : (2:ℤ)^k i ≤ (2:ℤ)^(k i+1) := by gcongr; norm_num; omega
    exact ⟨p.1.trans_le T,p.2.trans_le T⟩
  have j (i:J) : Dusk.mark (q i) =
      Grid.spell (Grid.fit (tally (k i+1),f i)) := by rw [spellG _ (fit_r ..),fit_small _ _ (g i)]
  refine ⟨q,?_,fun i=>?_⟩
  · unfold Satisfactory
    simp_rw [j]
    exact ((Regime.Has.pair (g:=fun i=>tally (k i+1)) (w.plus (.fix 1)) t).ez
      (Grid.fit_easy.compose Grid.spell_easy))
  unfold meaning q; rw [recovers _ (p i)]
  rw [show toC (content (f i))/(2:ℂ)^n i-x i=(toC (content (f i))-x i*(2:ℂ)^n i)/ (2:ℂ)^n i from by
    rw [sub_div,mul_div_cancel_right₀ _ (by norm_num)]]
  rw [norm_div,norm_pow,show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
  have C :(2:ℝ)*drop_ (n i)=2/(2:ℝ)^n i := by unfold drop_; rw [one_div,inv_pow,div_eq_mul_inv]
  rw [C]
  exact div_le_div_of_nonneg_right (e i) (by positivity)
end Star

end IntegerMultiplication
end Computability
end OAI
