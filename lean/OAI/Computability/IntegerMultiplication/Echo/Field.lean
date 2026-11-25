import OAI.Computability.IntegerMultiplication.Cap.Convolve
import OAI.Computability.IntegerMultiplication.Scale.Stars

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Echo
open Cap IntegerMultiplication.Fourier Finset Scale Param
variable {d:ℕ} (s:Bounds d)
abbrev Square := (i:Fin d) → Spot (s i) → Spot (s i) → ℂ

-- sup norm convenience
theorem segment (a : Square s) {w:ℝ} {x:Along s} (v:Bound x w) (p : ℝ)
    (t:∀ i b c,‖a i b c‖ ≤ p) (e:0≤p) (_z:0≤w) :
    Bound (strand s a x) ((space s:ℝ)*(p^d*w)) := by
  classical
  intro i; unfold strand
  calc
    _ ≤ ∑ _j: Vector_ s, p^d*w := by
      apply norm_sum_le_of_le
      intro j _
      rw [norm_mul,norm_prod]
      apply mul_le_mul _ (v _) (norm_nonneg _) (pow_nonneg e _)
      calc
       _ ≤ ∏ _i:Fin d,p := prod_le_prod₀ (fun _ _=> norm_nonneg _) (fun i _ => t _ _ _)
       _ = _ := by simp
    _ = _ := by rw [sum_const,card_univ,Cap.card,nsmul_eq_mul]

theorem phaseMeasure (q:Fin d→ℤ) {x:Along s} {w:ℝ} (z:0≤w) (t : Bound x w) :

    Bound (sing s q x) ((space s:ℕ)*w) := by
  change Bound (strand s (fun i=> Cap.kernel (q i)) x) _
  simpa only [one_pow,one_mul,sing] using
    segment s (fun i=>Cap.kernel (q i)) t 1 (fun i b c=> (phase_norm ..).le) (by norm_num) z

theorem sourced {J:Type} [Fintype J] (f p: J→ ℂ) {u:ℝ} (hu:0≤u)
    (h:∀ i,‖p i‖≤1) (g:∀ i,‖f i-p i‖≤u) (t:∀ i,‖f i‖≤2) :
    ‖∏ i,f i -∏ i,p i‖≤ Fintype.card J*(2:ℝ)^Fintype.card J*u := by
  classical
  suffices z : ∀ s:Finset J,‖∏ i∈s,f i -∏ i∈s,p i‖ ≤ s.card*(2:ℝ)^s.card*u from z univ
  intro s
  induction s using Finset.induction_on with
  | empty=> simp
  | insert i s v ih=>
    rw [prod_insert v, prod_insert v,card_insert_of_notMem v]
    let a:=∏ i∈s,f i
    let b:=∏ i∈s,p i
    change ‖f i*a-p i*b‖ ≤ _
    rw [show _ - _=(f i-p i)*a+p i*(a-b) from by ring]
    let k:ℕ:=s.card
    have W : ‖a‖ ≤ 2^k := by
      unfold a; rw [norm_prod]
      calc
       _ ≤ ∏ _i∈s,(2:ℝ) := prod_le_prod₀ (fun _ _=> norm_nonneg _) (fun i _=> t _)
       _ = _ := by simp [k]
    calc
     _ ≤ ‖(f i-p i)*a‖+‖p i*(a-b)‖ := norm_add_le _ _
     _ ≤ u*2^k+1*(k*2^k*u) := by simp only [norm_mul]; apply add_le_add (mul_le_mul (g i) W (norm_nonneg _) hu)
                                                 (mul_le_mul (h i) ih (norm_nonneg _) (by norm_num))
     _ ≤ _ := by push_cast
                 rw [pow_succ]
                 have Q : 0 ≤ (2:ℝ)^k*u := by positivity
                 have T : 0 ≤ (k:ℝ)*2^k*u := by positivity
                 unfold k at *; nlinarith

theorem sensitivity (a b : Square s) {u:ℝ} (hu : 0≤u) (hh:u≤1)
    (ht:∀ i j k,‖a i j k‖≤1) (h:∀ i j k, ‖b i j k-a i j k‖≤u)
    {x:Along s} {v:ℝ} (hx:Bound x v) :
    Gap (strand s b x) (strand s a x) (space s * ((d * (2:ℝ)^d*u)*v)) := by
  classical
  intro i
  unfold strand
  rw [← Finset.sum_sub_distrib]
  let w:ℝ:=d*(2:ℝ)^d*u
  calc
    _ ≤ ∑ j:Vector_ s,w*v := by
      apply norm_sum_le_of_le
      intro j _
      rw [← sub_mul,norm_mul]
      apply mul_le_mul _ (hx _) (norm_nonneg _) (by unfold w; positivity)
      have U := sourced (J:=Fin d) (fun k=> b k (i k) (j k)) (fun k=> a k (i k) (j k))
        hu (fun k=>ht k _ _) (fun k=> h k _ _)
        (fun k=> by
          have t:= norm_add_le (b k (i k) (j k)-a k (i k) (j k)) (a k (i k) (j k))
          rw [sub_add_cancel] at t
          linarith [h k (i k) (j k),ht k (i k) (j k)])
      simpa [w] using U
    _ = _ := by rw [sum_const,card_univ,Cap.card,nsmul_eq_mul]
end Echo

end IntegerMultiplication
end Computability
end OAI
