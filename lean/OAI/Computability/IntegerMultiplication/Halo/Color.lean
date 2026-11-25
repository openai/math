import OAI.Computability.IntegerMultiplication.Halo.Prism
import OAI.Computability.IntegerMultiplication.Grid.Comp

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Halo
open Param Scale Echo Cap IntegerMultiplication.Fourier Grid Axon Dusk Finset
variable {n k f:ℕ} (q:Fin f→Bits.Word) (b:ℕ→ Cone.G n)
abbrev xy (k f:ℕ):=Fin f→Spot (2^k)
noncomputable section
def color (x:xy k f→ Cone.G n) : xy k f→ Cone.G n :=
  Grid.azimuth (Scale.F n) q b (x ∘ pixel) ∘ pixel.symm
abbrev trueC:=Axon.mDFT (I:=Fin f) (k:=k) (Grid.Qu q)

theorem trueExpansion (x:xy k f→ℂ) (v:xy k f):
    trueC q x v=
      ∑ y:xy k f,(∏ i,Cap.kernel (-(Grid.Qu q i)) (v i) (y i))* x y := by
  unfold trueC Axon.mDFT Cap.kernel
  change ∑ y:xy k f,(∏ i,Axon.R k (Qu q i*_*_))* x y=_
  simp only [neg_neg]

theorem rayPay (t:(f+2)*k≤P n):
    raygain k f ≤ hi n 1 := by
  unfold raygain amps hi
  rw [show (4:ℝ)*2^f=2^(f+2) by rw [pow_add]; ring,← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by omega)
private theorem days (t:(f+2)*k≤P n):
    (2^k:ℝ)^f ≤ hi n 1 := by
  unfold hi; rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by nlinarith)
private theorem ribs (t:k≤P n):
    (k:ℝ) ≤ hi n 1 := by
  have t0:k < 2^P n := Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) t)
  unfold hi; rw [one_mul]; exact_mod_cast t0.le

theorem colorNorm {B:ℝ} (p:0≤B) (x y:xy k f→ℂ) (e:Gap x y B) (t:(f+2)*k≤P n):
    Gap (trueC q x) (trueC q y) (B*hi n 1) := by
  classical
  intro z; rw [trueExpansion,trueExpansion, ← Finset.sum_sub_distrib]
  let l(v:xy k f):= ∏ i,Cap.kernel (-(Grid.Qu q i)) (z i) (v i)
  change ‖∑ v:xy k f,(l v*x v-l v*y v)‖ ≤ _
  have o (v:xy k f):‖l v‖=1:=by simp [l,norm_prod,Cap.kernel,phase_norm]
  calc
    _ ≤ ∑ v:xy k f,B := norm_sum_le_of_le _ (fun v _=> by
      rw [← mul_sub,norm_mul,o]; simpa only [one_mul] using e v)
    _ = (2^k:ℝ)^f*B := by simp [xy,Spot]
    _ ≤ _ := by rw [mul_comm]; gcongr; exact days t

-- zap obeys Flow analog for farms on restricted index
theorem cert (odd:∀ i,Odd (Bits.value (q i)))
    (a:∀ i:Fin (2^k), ‖Cone.look n (b i)-Axon.R k (i.val:ℕ)‖ ≤err n)
    (t:(f+2)*k ≤ P n) (x:xy k f→ Cone.G n)
    {B:ℝ} (v:1≤B)(u:B≤hi n 750) (w:Bound (Cone.look n ∘ x) B):
    Bound (Cone.look n ∘ color q b x) (B*hi n 1) ∧
      Gap (Cone.look n ∘ color q b x) (trueC q (Cone.look n ∘ x)) (err n*B*hi n 2) := by
  let X:=x ∘ pixel
  have W : ∀ i:Sat (n:=k) (f:=f),‖Msec (Scale.F n) (X i)‖≤B := fun i=>w (pixel i)
  have rd : (2:ℝ)/2^Scale.F n ≤ err n := (round_n n).trans' (by
    unfold Star.drop_; rw [one_div,inv_pow,← div_eq_mul_inv]; gcongr; norm_num)
  have ex:=rayPay t
  have W0 : (2:ℝ)^Scale.F n*2*(B*raygain k f)+2<2^Scale.W n :=
    calc
    _ ≤ (hi n 1000)*(2:ℝ)^Scale.F n+2 := by
      rw [mul_assoc,mul_comm ((2:ℝ)^Scale.F n)]
      gcongr
      have y : 0≤raygain k f := by unfold raygain amps; positivity
      calc
        _ ≤ 2*(hi n 750 * hi n 1):=by have D:=hi1 n 750; gcongr
        _ = 2*hi n 751 := by rw [heightA]
        _ ≤ _ := (overhead ..).trans (hi_mono _ (by decide))
    _ < _ := model n
  have Q:=latitude (Scale.F n) q b odd (invp n).le v (err1 n) rd a X W W0
  constructor
  · intro i
    apply (Q.1 (pixel.symm i)).trans
    gcongr
  intro i
  have j:=Q.2 (pixel.symm i)
  suffices H : Grid.aim q (Msec (Scale.F n) ∘ X) (pixel.symm i) = trueC q (Cone.look n ∘ x) i by
    rw [H] at j
    refine j.trans ?_
    have R:= ribs (by nlinarith : k≤P n)
    have e : 0≤err n := (invp n).le
    calc
      _ ≤ err n * hi n 1 *(B*hi n 1) := by
        have D:=hi1 n 1
        have u : 0≤raygain k f := by unfold raygain amps; positivity
        gcongr
      _ = _ := by rw [show hi n 2=hi n 1*hi n 1 from (heightA n 1 1).symm]; ring
  unfold Grid.aim trueC
  change mDFT _ _ (pixel (pixel.symm _)) = _
  rw [Equiv.apply_symm_apply]
  congr 1
  funext v
  change Cone.look n (x (pixel (pixel.symm v)))=_
  rw [Equiv.apply_symm_apply]; rfl
end
end Halo

end IntegerMultiplication
end Computability
end OAI
