import OAI.Computability.IntegerMultiplication.Star.Stroke
import OAI.Computability.IntegerMultiplication.Grid.Stage

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Star
open Code Brief Staff Strip Carry Axon Dusk Grid IntegerMultiplication.Fourier
-- source fraction positive via construction
variable {J:Type} (r:Regime J)
variable (frac w k :J→ℕ)
variable (p:Realizes r frac) (u:Realizes r w) (v:Realizes r k)
variable (guard_ : ∀ i,(2:ℝ)*2^frac i+2 < 2^w i)
include p u guard_
variable {r}
theorem direction {a b:J→ℕ} (x:Figure r a) (y:Figure r b) (t:∀ i,0<b i) (e:∀ i,a i ≤ b i) :
    ∃ B:(i:J)→Grain (w i), Satisfactory w r B ∧
      ∀ i, ‖meaning (frac i) (w i) (B i)-Fourier.phase (b i) ((a i:ℕ):ℤ)‖ ≤ 3*drop_ (frac i) := by
  let f (i:J):ℝ := (a i:ℝ)/ (b i:ℝ)
  have q : Blot r f := (Blot.natural x).ratio (Blot.natural y) (fun i=> by exact_mod_cast t i)
  have d i : |f i| ≤ 1 := by
    unfold f
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one (by exact_mod_cast t i)).2 (by exact_mod_cast e i)
  let n i := 34+frac i
  have T:Realizes r n := Realizes.plus (.fix 34) p
  let g i := needle (n i) (f i)
  have U i : ‖g i-Fourier.phase (b i) ((a i:ℕ):ℤ)‖≤ drop_ (frac i) := by
    unfold g Fourier.phase
    push_cast
    apply (tip (n:=n i) (by unfold n; omega) (d i)).trans
    unfold n drop_
    rw [pow_add,← mul_assoc]
    norm_num
  have h i : ‖g i‖≤2 := by
    let A:= Fourier.phase (b i) ((a i:ℕ):ℤ)
    have Q:=norm_add_le (g i-A) A
    rw [sub_add_cancel,phase_norm] at Q
    linarith only [Q,U i,drop1 (frac i)] -- A local def
  obtain ⟨z,o,H⟩ := stroke g frac w p u (critical _ q _ T)
    (fun i=> by apply lt_of_le_of_lt ?_ (guard_ i); gcongr; exact h i)
  refine ⟨z,o,fun i=>?_⟩
  let A:= Fourier.phase (b i) ((a i:ℕ):ℤ)
  let X:=meaning (frac i) (w i) (z i)
  rw [show X - A=(X-g i)+(g i-A) from by ring]
  calc
    _ ≤ ‖X-g i‖+‖g i-A‖ := norm_add_le _ _
    _ ≤ _ := by linarith only [H i,U i]

include v
theorem shelving (Q : Realizes r (fun i=>2^k i)) :
    ∃ B:(i:J)→ℕ→ Grain (w i),
      r.Has (fun i=>Grid.telex (frac i) (k i) (B i)) ∧
      ∀ (i:J) (g:Fin (2^k i)), ‖meaning (frac i) (w i) (B i g)-Axon.R (k i) (g.val:ℕ)‖≤
        3*drop_ (frac i) := by
  classical
  let n (i:J):=2^k i
  let E := signal n Q
  let X := Across n
  let a : X→J := Sigma.fst
  have t := floor_ n Q
  let V {s:J→ℕ} (h:Realizes r s) : Realizes E (s ∘ a) := landing n Q s h
  let z (i:X):=i.2.val
  let t':Realizes E z:=t
  obtain ⟨b,t,e⟩ := direction (frac ∘ a) (w ∘ a) (V p) (V u) (fun i=>guard_ (a i))
    (Figure.of_spoken t') (Figure.of_spoken (V Q)) (fun i=>pow_pos (by decide) _) (fun i=>i.2.isLt.le)
  let B (i:J) (l:ℕ) : Grain (w i) := if h:l<n i then b ⟨i,⟨l,h⟩⟩ else 0
  have q (i:J) (l : Fin (n i)) : B i l= b ⟨i,l⟩ := by unfold B; simp
  refine ⟨B,?_,fun i g=>?_⟩
  · unfold telex
    apply harvest n Q
    have A := (Figure.of_spoken t').phrase_ (V v) (fun i=>i.2.isLt)
    have H := A.pair (Strip.Regime.Has.pair (g:=fun i=> tally (frac (a i))) (V p) t)
    convert H using 1
    funext ⟨i,c⟩
    exact congrArg (fun y=> (Bits.phrase (k i) c.val,tally (frac i),mark y)) (q i c)
  rw [q]; exact e ⟨i,g⟩
end Star

end IntegerMultiplication
end Computability
end OAI
