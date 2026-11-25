import OAI.Hierarchy.GridDyadicScale
import OAI.Hierarchy.GridLensWeights

namespace OAI
/-! # Uniform rescaling for reuse of a grid of arbitrary subpower side length -/

namespace Hierarchy.GridScale
open Filter
noncomputable section

def reuseMajorant (g B : ℕ → ℕ) (w : ℕ) := max (g w) (B w ⌈/⌉ 2^w)

private theorem majorant_envelopes {g B : ℕ → ℕ} {D : ℕ → ℝ}
    (growth : ∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop,
      (g w:ℝ) ≤ dyad (ε*w) ∧ (B w:ℝ) ≤ dyad ((1+ε)*w) ∧ dyad ((1-ε)*w) ≤ D w) :
    Envelopes (reuseMajorant g B) D := by
  intro ε he
  have hpos : 0<ε/2 := half_pos he
  obtain ⟨N,hN⟩ := exists_nat_gt (2/ε)
  filter_upwards [growth ε he, growth (ε/2) hpos, eventually_ge_atTop N] with w full half hw
  let t := dyad (ε/2*w)
  have wn : (N:ℝ) ≤ w := by exact_mod_cast hw
  have exp : 1 ≤ ε/2*w := by nlinarith only [(div_lt_iff₀ he).mp hN,mul_le_mul_of_nonneg_left wn he.le]
  have ht : 2 ≤ t := (by simpa [t,dyad] using dyad_mono exp)
  have lt : t+1 ≤ dyad (ε*w) := by
    calc
      _ ≤ t*t := by nlinarith [mul_nonneg (by linarith : 0≤t) (by linarith : 0≤t-2)]
      _ = _ := by dsimp only [t]; rw [dyad_add]; congr 1; ring
  have bv : (B w:ℝ) ≤ (2:ℝ)^w*t := by
    calc
      _ ≤ dyad ((1+ε/2)*w) := half.2.1
      _ = dyad w*t := by dsimp only [t]; rw [dyad_add]; congr 1; ring
      _ = _ := by simp [dyad]
  have integral : B w ≤ 2^w*⌈t⌉₊ := by
    exact_mod_cast bv.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil t) (by positivity))
  have book : B w ⌈/⌉ 2^w ≤ ⌈t⌉₊ := (ceilDiv_le_iff_le_mul (Nat.two_pow_pos _)).mpr integral
  refine ⟨?_,full.2.2⟩
  change (max (g w) (B w ⌈/⌉ 2^w):ℕ) ≤ dyad (ε*w)
  rw [Nat.cast_max]
  refine max_le full.1 ?_
  exact (show ((B w ⌈/⌉ 2^w:ℕ):ℝ) ≤ ⌈t⌉₊ by exact_mod_cast book).trans
    ((Nat.ceil_lt_add_one (by linarith : 0≤t)).le.trans lt)

/-- A common radius for every wiring on a prescribed subpower-sized grid.
It is subpower, the final gap is near volume, and both lens losses are
small enough to apply `GridLens.reuse_gap` at that very radius. -/
theorem uniform_reuse {g B : ℕ → ℕ} {D : ℕ → ℝ} (k : ℕ)
    (growth : ∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop,
      (g w:ℝ) ≤ dyad (ε*w) ∧ (B w:ℝ) ≤ dyad ((1+ε)*w) ∧ dyad ((1-ε)*w) ≤ D w) :
    ∃ R : ℕ → ℕ, (∀ ε : ℝ, 0<ε → ∀ᶠ w : ℕ in atTop,
        (R w:ℝ) ≤ dyad (ε*w) ∧ dyad ((1-ε)*w) ≤ D w/(2*R w)) ∧
      ∀ᶠ w : ℕ in atTop, 8*g w ≤ R w ∧
        (18:ℝ)*(k-1:ℕ)*((g w:ℝ)^(k-1)*B w)*(g w:ℝ)^2/R w ≤ D w/4 ∧
        (2:ℝ)*k*R w*(g w:ℝ)^k ≤ D w/4 := by
  let Q := reuseMajorant g B
  have env : Envelopes Q D := majorant_envelopes growth
  let a := overhead Q D
  let R := fun w => radius k (a w)
  refine ⟨R, ?_, ?_⟩
  · intro ε he
    filter_upwards [uniform_sizes env k he, real_sublinear env (10*k+19) he,
      bounds env, (tendsto_atTop.mp (grows env)) 1, sublinear env 1] with w sizes budget saved age room
    refine ⟨sizes.2.1, ?_⟩
    have aw : a w ≤ w := by simpa [a] using room
    have ageR : (1:ℝ) ≤ a w := by exact_mod_cast age
    change (((10*k+19:ℕ):ℝ)*(a w:ℝ) ≤ ε*w) at budget
    push_cast at budget
    have lift : (R w:ℝ) = dyad ((10*(k:ℝ)+16)*(a w)) := by
      change ((2^((10*k+16)*a w):ℕ):ℝ) = _
      rw [dyad_nat]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    have two : dyad 1 = 2 := by norm_num [dyad]
    apply (le_div_iff₀ (by dsimp [R,radius]; positivity)).mpr
    calc
      _ = dyad ((1-ε)*w) * (dyad 1 * dyad ((10*(k:ℝ)+16)*(a w))) := by
        rw [two,lift]
      _ = dyad ((1-ε)*w + (1+(10*(k:ℝ)+16)*(a w))) := by rw [dyad_add,dyad_add]
      _ ≤ dyad (w-a w:ℕ) := by
        apply dyad_mono
        rw [Nat.cast_sub aw]
        nlinarith only [budget,ageR]
      _ = (2:ℝ)^(w-a w) := by simp [dyad]
      _ ≤ _ := saved.2.1
  · filter_upwards [bounds env, sublinear env (100*k+300), (tendsto_atTop.mp (grows env)) 3,
      polynomial env (72*(k+1)) 0] with w saved fit age constant
    let h := a w
    have ha : 3 ≤ h := age
    have mature : (100*k+300)*h ≤ w := fit
    have room : h ≤ w := (Nat.le_mul_of_pos_left _ (by positivity : 0<100*k+300)).trans mature
    have less := Nat.sub_add_cancel room
    have gcap : g w ≤ 2^h := (le_max_left _ _).trans saved.1
    have bcap : B w ≤ 2^(w+h) := by
      rw [pow_add]
      apply (ceilDiv_le_iff_le_mul (Nat.two_pow_pos _)).mp
      exact (le_max_right _ _).trans saved.1
    have tariff : 72*(k+1) ≤ 2^h := by simpa [h,a] using constant
    have price : 72*(k-1) ≤ 2^h := (Nat.mul_le_mul_left 72 (by omega)).trans tariff
    have rent : 8*k ≤ 2^h := (by omega : 8*k ≤ 72*(k+1)).trans tariff
    have distant : 8*g w ≤ R w := by
      change 2^3*g w ≤ 2^((10*k+16)*h)
      calc
        _ ≤ 2^3*2^h := Nat.mul_le_mul_left _ gcap
        _ = 2^(3+h) := (pow_add ..).symm
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith only [ha,Nat.zero_le (k*h)])
    have rail : 72*(k-1)*((g w)^(k-1)*B w)*(g w)^2 ≤ 2^(w-h)*R w := by
      calc
        _ ≤ 2^h*((2^h)^(k-1)*2^(w+h))*(2^h)^2 :=
          Nat.mul_le_mul (Nat.mul_le_mul price (Nat.mul_le_mul (Nat.pow_le_pow_left gcap _) bcap))
            (Nat.pow_le_pow_left gcap _)
        _ = 2^(h+(h*(k-1)+(w+h))+h*2) := by simp only [pow_add,pow_mul]
        _ ≤ 2^((w-h)+(10*k+16)*h) := by
          apply Nat.pow_le_pow_right (by decide)
          nlinarith only [less, Nat.mul_le_mul_left h (Nat.sub_le k 1),Nat.zero_le (k*h)]
        _ = _ := pow_add ..
    have count : 8*k*R w*(g w)^k ≤ 2^(w-h) := by
      calc
        _ ≤ 2^h*2^((10*k+16)*h)*(2^h)^k :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ rent) (Nat.pow_le_pow_left gcap _)
        _ = 2^(h+(10*k+16)*h+h*k) := by simp only [pow_add,pow_mul]
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith only [mature,less,Nat.zero_le (k*h)])
    have rr : (72:ℝ)*(k-1:ℕ)*((g w:ℝ)^(k-1)*B w)*(g w:ℝ)^2 ≤ (2:ℝ)^(w-h)*(R w:ℝ) := by exact_mod_cast rail
    have cc : (8:ℝ)*k*(R w:ℝ)*(g w:ℝ)^k ≤ (2:ℝ)^(w-h) := by exact_mod_cast count
    have safe : (2:ℝ)^(w-h) ≤ D w := saved.2.1
    have rpos : (0:ℝ)<(R w:ℝ) := by exact_mod_cast Nat.two_pow_pos ((10*k+16)*h)
    refine ⟨distant, (div_le_iff₀ rpos).mpr ?_, ?_⟩
    · nlinarith only [rr, mul_le_mul_of_nonneg_right safe rpos.le]
    · linarith only [cc,safe]


end
end Hierarchy.GridScale

end OAI
