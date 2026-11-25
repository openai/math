import OAI.ThreeFlat.Diagonal.RefreshSlotRewrite
import OAI.ThreeFlat.Diagonal.MotifChosenEnergy

namespace OAI
/-! # Quadratic energy of each physical degree-refresh term -/

namespace ThreeFlat.Diagonal.RefreshTies

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction Expander
open Computability.VPVNP.MotifGrid Computability.VPVNP.MotifWidths MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

variable {V L : Type} [Fintype V] [Fintype L] {m h : ℕ}
variable (c : Fin m → Fin m → ℕ) (π : Equiv.Perm (Address (V × L) m))
variable (w : Address (V × L) m → ℕ)

abbrev demandNorm (u : V × L) :=
  widthNorm (fun _ : Bool × Fin m × Fin m => (1:ℝ)) (fun e => (w (addr π u e) : ℝ))

/-- Dense demand axes in all port blocks give exactly twice the old width
energy, including the two incidences of each self-tie. -/
theorem total_demand :
    (∑ u, (demandNorm π w u)^2) = 2*(∑ e, (w e : ℝ)^2) := by
  simpa only [demandNorm,norm_sq _ _ (fun _ => zero_lt_one),div_one] using
    dense_charge π (fun e => (w e : ℝ)^2)

/-- Convert the normalized per-block motif estimate to actual mass and sum
all internal arcs. -/
theorem internal_energy (s : V × L → Arc c → ℕ) {d₀ p H C : ℝ}
    (hm : 0 < m) (hd : 0 < d₀) (hp : 0 < p)
    (localBound : ∀ u, widthNorm (fun _ : Arc c => (m : ℝ)/d₀) (fun e => (s u e : ℝ))^2 ≤
      H*(demandNorm π w u)^2 + C) :
    (∑ u, ∑ a, (s u a : ℝ)^2/(m*p/d₀)) ≤
      2*H*(∑ e, (w e : ℝ)^2/p) + Fintype.card (V × L)*(C/p) := by
  have qpos : 0 < (m : ℝ)/d₀ := by positivity
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => localBound u)
  simp only [norm_sq _ _ (fun _ => qpos),Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,total_demand π w] at hsum
  have assoc (x : ℝ) : x/(m*p/d₀) = (x/((m:ℝ)/d₀))/p := by
    rw [div_div,div_mul_eq_mul_div]
  calc
    _ = (∑ u, ∑ a, (s u a : ℝ)^2/((m:ℝ)/d₀))/p := by simp only [Finset.sum_div,assoc]
    _ ≤ (H*(2*∑ e, (w e : ℝ)^2))/p + ((Fintype.card (V × L) : ℝ)*C)/p := by
      simpa only [add_div] using div_le_div_of_nonneg_right hsum hp.le
    _ = _ := by rw [← Finset.sum_div]; ring

/-- The factor in front of the old energy is independent of the temporary
port count. The normalized mass identity cancels the block count exactly in
the additive error. -/
theorem bounded_refresh (rows : ∀ v, ∑ j, c v j = h) (pad : ℕ) (s : V × L → Arc c → ℕ)
    {d₀ H C : ℝ} (hm : 0 < m) (hd : 0 < d₀) (uNonempty : 0 < Fintype.card (V × L))
    (localBound : ∀ u, widthNorm (fun _ : Arc c => (m:ℝ)/d₀) (fun e => (s u e : ℝ))^2 ≤
      H*(demandNorm π w u)^2+C) :
    let P : ℝ := (Fintype.card (V × L) : ℝ)*m
    let p : ℝ := 1/(P*m)
    (∑ a, (freshWidth c rows (termWidth c w s) pad a : ℝ)^2/(m*p/d₀)) ≤
      (d₀+2*H)*(∑ e, (w e : ℝ)^2/p) + C*P^2 := by
  intro P p
  have hp : 0 < p := by dsimp [p,P]; positivity
  have ext := numbered_energy_le c rows pad w s hp hd
  have ins := internal_energy c π w s hm hd hp localBound
  have err : (Fintype.card (V × L) : ℝ)*(C/p) = C*P^2 := by
    dsimp [P,p]
    rw [div_div_eq_mul_div,div_one]
    ring
  rw [err] at ins
  linarith

omit [Fintype V] [Fintype L] in
/-- The normalized estimate needed by `bounded_refresh` follows uniformly
from the chosen integer copy counts and the finite base supply norm. The
output widths are the actual histogram payload plus its selector bits. -/
theorem histogram_refresh_bound {d₀ R H : ℝ} {l bits : ℕ}
    (hm : 0 < m) (hd : 0 < d₀) (hl : 0 < l) (hR : 0≤R)
    (gap : (R+bits/(l:ℝ)*widthNorm (fun _ : Arc c => (m:ℝ)/d₀) (fun _ => 1))^2 < H) :
    ∃ C : ℝ, ∀ (T : V × L → Type) [∀ u, Fintype (T u)] [∀ u, DecidableEq (T u)]
      (r : V × L → ℕ) (out : ∀ u, T u → Arc c → ℕ),
      (∀ u, r u ≤ copies (demandNorm π w u) l) →
      (∀ u j, widthNorm (fun _ : Arc c => (m:ℝ)/d₀) (fun e => (out u j e : ℝ)) ≤ (l:ℝ)*R) →
      ∀ (z : ∀ u, Histogram (T u) (r u)) u,
        widthNorm (fun _ : Arc c => (m:ℝ)/d₀)
          (fun e => ((histWidth (out u) (z u) e+r u*bits : ℕ):ℝ))^2 ≤ H*(demandNorm π w u)^2+C := by
  obtain ⟨C,hC⟩ := MotifIntegerChoice.chosen_histogram_energy
    (q := fun _ : Arc c => (m:ℝ)/d₀) (fun _ => by positivity) hl hR gap
  refine ⟨C,?_⟩
  intro T _ _ r out count radius z u
  exact hC _ (Real.sqrt_nonneg _) _ (count u) (T u) (out u) (radius u) (z u)

/-- The additive constant is chosen before the current graph, its blocks,
and their actual input widths. The restored mass is the reciprocal of the
actual new arc count. Every histogram term obeys the same bound. -/
theorem histogram_stage {m h : ℕ} (c : Fin m → Fin m → ℕ) (rows : ∀ i, ∑ j, c i j = h)
    (pad : ℕ) {R H : ℝ} {l bits : ℕ} (hm : 0 < m) (hl : 0 < l) (hR : 0≤R)
    (gap : (R+bits/(l:ℝ)*widthNorm (fun _ : Arc c => (m:ℝ)/(1+h+pad)) (fun _ => 1))^2 < H) :
    ∃ C : ℝ, 0≤C ∧ ∀ (V L : Type) [Fintype V] [Fintype L], 0 < Fintype.card (V × L) →
      ∀ (π : Equiv.Perm (Address (V × L) m)) (w : Address (V × L) m → ℕ)
        (T : V × L → Type) [∀ u, Fintype (T u)] [∀ u, DecidableEq (T u)]
        (r localBits : V × L → ℕ) (out : ∀ u, T u → Arc c → ℕ),
        (∀ u, localBits u ≤ bits) → (∀ u, r u ≤ copies (demandNorm π w u) l) →
        (∀ u j, widthNorm (fun _ : Arc c => (m:ℝ)/(1+h+pad)) (fun e => (out u j e : ℝ)) ≤ (l:ℝ)*R) →
        ∀ (z : ∀ u, Histogram (T u) (r u)),
        let P : ℝ := (Fintype.card (V × L) : ℝ)*m
        let s := fun u e => histWidth (out u) (z u) e + r u*localBits u
        (∑ a, (freshWidth c rows (termWidth c w s) pad a : ℝ)^2/(1/(P*(1+h+pad)))) ≤
          ((1+h+pad)+2*H)*(∑ e, (w e : ℝ)^2/(1/(P*m))) + C*P^2 := by
  let d₀ : ℝ := 1+h+pad
  have hd : 0 < d₀ := by dsimp [d₀]; positivity
  let q := fun _ : Arc c => (m:ℝ)/d₀
  have hq (e : Arc c) : 0 < q e := by dsimp [q]; positivity
  obtain ⟨C,hC⟩ := MotifIntegerChoice.chosen_histogram_energy hq hl hR gap
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro V L _ _ hU π w T _ _ r localBits out hbits count radius z P s
  have localBound (u : V × L) : widthNorm q (fun e => (s u e : ℝ))^2 ≤ H*(demandNorm π w u)^2+max C 0 := by
    have hb := hC _ (Real.sqrt_nonneg _) _ (count u) (T u) (out u) (radius u) (z u)
    refine le_trans ?_ (hb.trans (add_le_add le_rfl (le_max_left C 0)))
    apply pow_le_pow_left₀ (Real.sqrt_nonneg _) _ 2
    apply norm_mono _ _ _ hq (fun _ => Nat.cast_nonneg _)
    intro e
    exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_left (r u) (hbits u)) _
  have bound := bounded_refresh c π w rows pad s hm hd hU localBound
  have hP : 0 < P := by dsimp [P]; positivity
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  have he : (m:ℝ)*(1/(P*m))/d₀ = 1/(P*d₀) := by field_simp [hP.ne',hm'.ne',hd.ne']
  change (∑ a, (freshWidth c rows (termWidth c w s) pad a : ℝ)^2 / (1/(P*d₀))) ≤ _
  rw [← he]
  exact bound

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
