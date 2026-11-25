import OAI.Computability.IntegerMultiplication.Fourier.Mixer

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open Finset Real
variable {s t : ℕ} [NeZero s] [NeZero t]

-- Lipschitz estimate given a uniform lower bound on weight.
theorem pick_gap {B C : ℝ} {D : ℕ} {f g : Arr t ℂ} (e : s≤t) (h : Gap f g B)
    (hc : ∀ i : Spot s, 1/(coef D (delta s t i))≤C) (_hb : 0≤B) (hC : 0≤C) :
    Gap (pickDiv e D f) (pickDiv e D g) (C * B) := by
  intro i
  dsimp only [pickDiv]
  rw [← sub_div,norm_div,norm_mul]
  have hd := coef_nonneg D (delta s t i)
  simp only [Complex.norm_natCast, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd]
  have ht : 1≤(t:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  let X := ‖f (pick s t e i) - g (pick s t e i)‖
  let u := coef D (delta s t i)
  have hX : X≤B := h _
  change X/(t*u:ℝ) ≤ _
  rw [show X/(t*u:ℝ) = (1/(t:ℝ))*(1/u)*X by
    simp [div_eq_mul_inv, mul_comm]]
  apply mul_le_mul _ hX (norm_nonneg _) hC
  calc
    _ ≤ 1*(1/u) := by
      gcongr
      exact div_le_self (by simp) ht
    _ ≤ C := by rw [one_mul]; exact hc i

noncomputable def restore (e : s≤t) (D J k : ℕ) (v : Arr t ℂ) : Arr s ℂ :=
  iter t D (nhood J) (pickDiv e D v) k

omit [NeZero t] in
theorem pick_zero {D : ℕ} {e : s≤t} : pickDiv e D 0 = 0 := by ext; simp [pickDiv]

theorem restore_gap {X C : ℝ} (e : s≤t) {D J k} {v u : Arr t ℂ} (h : Gap v u X)
    (hb : ∀ i : Spot s, ∑ j ∈ nhood J, ratio t D (delta s t i) j≤1/2)
    (hc : ∀ i : Spot s, 1/(coef D (delta s t i))≤C) (hX : 0≤X) (hC : 0≤C) :
    Gap (restore e D J k v) (restore e D J k u) (2*(C*X)) :=
  iter_gap hb (pick_gap e h hc hX hC) (mul_nonneg hC hX) k

theorem restore_bound {X C : ℝ} (e : s≤t) {D J k} {v : Arr t ℂ} (h : Bound v X)
    (hb : ∀ i : Spot s, ∑ j ∈ nhood J, ratio t D (delta s t i) j≤1/2)
    (hc : ∀ i : Spot s, 1/(coef D (delta s t i))≤C) (hX : 0≤X) (hC : 0≤C) :
    Bound (restore e D J k v) (2*(C*X)) := by
  have he := restore_gap (k:=k) e (u := 0) (X:=X) (by simpa only [Gap,Pi.zero_apply,sub_zero,Bound] using h)
    hb hc hX hC
  simpa [Bound,Gap,restore,pick_zero] using he

/-- Quantitative identity with parameters describing the off-diagonal decay.
C is the bound on diagonal amplification, q on the J-window mixing, and
r on the remaining tail (one bound for each row in both cases).
No numerical precision yet; all the error here is finite resampling.
-/
theorem line_est (e : s≤t) {k D J L : ℕ} {q r C B : ℝ}
    (hLs : 2*L<s) (hs : s≤D) (hJ : J≤2*D)
    (hq₀ : 0≤q) (hq : q≤1/2) (hC : 0 ≤ C)
    (hr : 0≤r)
    (hc : ∀ i : Spot s, 1/(coef D (delta s t i))≤C)
    (hq' : ∀ i : Spot s, ∑ j ∈ nhood J, ratio t D (delta s t i) j≤q)
    (hr' : ∀ i : Spot s, ∑ j ∈ nhood (2*D) \ nhood J, ratio t D (delta s t i) j≤r)
    {f : Arr s ℂ} (h : Bound f B) (he : 0≤B) :
    Gap (restore e D J k (dft t (-(s:ℤ)) (sample s t D L f)))
      (dft s t f)
      (2*(C*(t*((s:ℝ)*Real.exp (-(4:ℝ)*D*(L:ℕ)^2/(s:ℕ)^2)*B)))+
       q^k*((q+r)*((s:ℝ)*B))+2*(r*((s:ℝ)*B))) := by
  let w₁ := dft t (-(s:ℤ)) (sample s t D L f)
  let w := dft t (-(s:ℤ)) (grow s t D f)
  let v := dft s t f
  let d := nhood J
  let u := nhood (2*D)
  have hwd := dft_gap (-(s:ℤ)) (sample_gap_grow (t:=t) D L hLs h he)
  have hqest i := (hq' i).trans hq
  have hE : 0≤ (t:ℝ)*(s*Real.exp (-(4:ℝ)*D*(L:ℕ)^2/(s:ℕ)^2)*B) := by positivity
  have hh := restore_gap (k:=k) e hwd hqest hc hE hC
  have hb := dft_bound (↑t:ℤ) h
  have hpos : 0≤ (s:ℝ)*B := by positivity
  have hrb := off_bound (d := u \ d) hr' hb hpos
  have hds := off_bound hq' hb hpos
  have hpick : pickDiv e D w = v + off t D d v + off t D (u \ d) v := by
    rw [show pickDiv e D w=v+off t D u v from diag e hs _]
    funext x
    simp only [Pi.add_apply,off]
    have hsub : d ⊆ u := by
      intro i hi
      simp only [d,nhood,mem_erase, ne_eq,mem_rad] at hi
      simp only [u,nhood,mem_erase,ne_eq,mem_rad]
      omega
    rw [add_assoc, add_comm (∑ i ∈ d, _), sum_sdiff hsub]
  have hsolve := solve hq₀ hq hq' (v:=v) (w := pickDiv e D w) (E:=r*(s*B))
    (by
      intro i
      rw [hpick, Pi.add_apply, add_sub_cancel_left]
      exact hrb i)
    (by positivity)
    (B := (q+r)*(s*B))
    (by
      intro i
      rw [hpick, Pi.add_apply, Pi.add_apply, add_assoc,add_sub_cancel_left,add_mul]
      exact (norm_add_le ..).trans (add_le_add (hds i) (hrb i)))
    (by positivity)
    k
  rw [add_assoc]
  exact hh.trans hsolve

end Fourier

end IntegerMultiplication
end Computability
end OAI
