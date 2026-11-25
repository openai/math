import OAI.Computability.IntegerMultiplication.Fourier.Truncate

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open Finset Real
variable {s t : ℕ} [NeZero s] [NeZero t]

noncomputable def pickDiv (e : s ≤ t) (D : ℕ) (w : Arr t ℂ) (x : Spot s) : ℂ :=
  w (pick s t e x) / ((t:ℂ)*(coef D (delta s t x) : ℂ))

noncomputable def off (t D : ℕ) (d : Finset ℤ) (w : Arr s ℂ) (x : Spot s) : ℂ :=
  ∑ j ∈ d, (ratio t D (delta s t x) j : ℂ)*w (wrap s (rep x+j))

noncomputable def nhood (L : ℕ) := (rad L).erase 0

theorem diag {D : ℕ} (h : s≤t) (hd : s≤D) (f : Arr s ℂ) :
    pickDiv h D (dft t (-(s:ℤ)) (grow s t D f)) =
      dft s t f + off t D (nhood (2*D)) (dft s t f) := by
  funext y
  let δ := delta s t y
  let x := pick s t h y
  have he : (s:ℤ)*rep x=(t:ℤ)*rep y+δ := by
    dsimp [x, δ, delta, pick, rep]
    omega
  have hh : δ∈rad D := by
    have hm := delta_small s t y
    change 2*|δ|≤(s:ℤ) at hm
    simp
    exact abs_le.mp (show |δ|≤ (D:ℤ) by linarith [show (s:ℤ)≤(D:ℤ) from by exact_mod_cast hd, abs_nonneg δ])
  let ep := dft s t f
  change dft t _ _ x / _ = ep y + off t D _ ep y
  rw [selected_grow_dft D f _ _ _ he hh,← Finset.add_sum_erase _ _ (show (0:ℤ) ∈ rad (2*D) by simp)]
  change (_+_) / ((t:ℂ)*↑(coef D δ)) = _
  simp only [mul_zero,sub_zero,add_zero,wrap_rep,add_div,Finset.sum_div,nhood,off]
  congr 1
  · dsimp only [ep]
    field [show (t:ℂ)≠0 from Nat.cast_ne_zero.mpr (NeZero.ne t),
      show (coef D δ:ℂ)≠0 from by exact_mod_cast (coef_pos hh).ne']
  · refine sum_congr rfl ?_
    intro i _
    dsimp only [ratio,ep]
    norm_cast -- inspect
    change _ = (((coef D (δ - (t:ℤ)*i) / coef D δ : ℝ):ℂ) * _)
    push_cast
    field [show (t:ℂ)≠0 from Nat.cast_ne_zero.mpr (NeZero.ne t),
      show (coef D δ:ℂ)≠0 from by exact_mod_cast (coef_pos hh).ne']

omit [NeZero t] in
theorem off_gap {q B : ℝ} {f g : Arr s ℂ} {D : ℕ} {d : Finset ℤ} (hb : ∀ x : Spot s,
    ∑ j ∈ d, ratio t D (IntegerMultiplication.Fourier.delta s t x) j ≤ q) (h : Gap f g B) (e : 0≤B) :
    Gap (off t D d f) (off t D d g) (q*B) := by
  intro i
  exact Gap.of_weight (w:=fun j => (ratio t D (IntegerMultiplication.Fourier.delta s t i) j : ℂ)) h e
    (by simpa [abs_of_nonneg (ratio_nonneg ..)] using hb i) _

omit [NeZero t] in
@[simp]
theorem off_zero {D d} : off t D d (0 : Arr s ℂ) = 0 := by unfold off; ext; simp

omit [NeZero t] in
theorem off_bound {q B : ℝ} {f : Arr s ℂ} {D : ℕ} {d : Finset ℤ} (hb : ∀ x : Spot s,
    ∑ j ∈ d, ratio t D (delta s t x) j ≤ q) (h : Bound f B) (e : 0≤B) :
    Bound (off t D d f) (q*B) := by
  intro i
  exact Bound.weight (w:=fun j => (ratio t D (delta s t i) j : ℂ)) h e
    (by simpa [abs_of_nonneg (ratio_nonneg ..)] using hb i) _

/-- Each term uses data within the designated offsets d, though this is not the eventual
precomputed/flattened matrix definition. -/
noncomputable def iter (t D : ℕ) (d : Finset ℤ) (v : Arr s ℂ) : ℕ → Arr s ℂ
  | 0 => v
  | k+1 => v - off t D d (iter t D d v k)

omit [NeZero t] in
/-- For a sufficiently contractive mixer, unrolling the inverse gives a bounded
operator even as k grows. -/
theorem iter_gap {B : ℝ} {f g : Arr s ℂ} {D : ℕ} {d : Finset ℤ} (hb : ∀ x : Spot s,
    ∑ j ∈ d, ratio t D (delta s t x) j ≤ 1/2) (h : Gap f g B) (e : 0≤B) (k : ℕ) :
    Gap (iter t D d f k) (iter t D d g k) (2*B) := by
  induction k with
  | zero => exact h.mono (by linarith)
  | succ k ih =>
    have he := off_gap hb ih (by linarith)
    intro x
    rw [iter,iter,Pi.sub_apply,Pi.sub_apply, show f x-_-(g x-_) =
        (f x-g x) - ((off t D d (iter t D d f k) x)-(off t D d (iter t D d g k) x)) by ring]
    refine (norm_sub_le ..).trans ?_
    have := he x
    have := h x
    linarith

omit [NeZero t] in
@[simp]
theorem iter_zero {D d} (k) : iter t D d (0 : Arr s ℂ) k=0 := by
  induction k <;> simp [*,iter]

-- last file block uses B for recover input, and condition q,B nonneg
omit [NeZero t] in
/-- Suppose the available data already differs by at most E from the near-neighbor
corruption of v. Iterate k more corrections, starting from error at most B.
Then the inverse loses only a constant factor on E.
-/
theorem solve {D : ℕ} {d : Finset ℤ} {q E B : ℝ} {w v : Arr s ℂ}
    (hq₀ : 0≤q) (hq : q≤1/2)
    (hb : ∀ x : Spot s, ∑ j ∈ d, ratio t D (delta s t x) j≤q)
    (hin : Gap w (v+off t D d v) E) (he : 0≤E)
    (h0 : Gap w v B) (he' : 0≤B) (k : ℕ) :
    Gap (iter t D d w k) v (q^k * B + 2*E) := by
  induction k with
  | zero =>
    exact h0.mono (by simp; linarith) -- simp?
  | succ k ih =>
    have hm : 0≤q^k*B := by positivity
    have h := off_gap hb ih (by linarith)
    intro x
    calc
      _ = ‖(w x-(v+off t D d v) x) -
          (off t D d (iter t D d w k) x - off t D d v x)‖ := by
            rw [iter,Pi.sub_apply,Pi.add_apply]; congr 1; ring
      _ ≤ ‖w x-(v+off t D d v) x‖+
          ‖off t D d (iter t D d w k) x - off t D d v x‖ := norm_sub_le ..
      _ ≤ q^(k+1)*B+2*E := by
        have hz := hin x
        have hh := h x
        rw [pow_succ]
        nlinarith

end Fourier

end IntegerMultiplication
end Computability
end OAI
