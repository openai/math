import OAI.Computability.MultitapeWeakETH.GraphGeometry

/-! # Placement on the vertices of an arbitrary bounded-degree multigraph -/

namespace OAI.Computability.MultitapeWeakETH

open Finset MetricKMedian.PCP VPVNP.SpectralGeometry
open scoped BigOperators

set_option maxRecDepth 4096

private theorem choose_padding (e : ℕ) :
    let C := 2*(2:ℝ)^e/(2:ℝ)^88
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ k : ℕ,
      let P := 2^(176*k)
      let β := (176*k:ℕ)/(10000*((e:ℝ)+3))
      n ≤ P ∧ 10000*(e+3) ≤ 176*k ∧ C ≤ β ∧
        (2:ℝ)^e*P/β ≤ K*n/Real.log n ∧ P*(C/β) ≤ K*n/Real.log n := by
  intro C
  let H := 10000*((e:ℝ)+3)
  let R := (2:ℝ)^177
  have hp : 0 < H := by dsimp [H]; positivity
  have hc : 0 < C := by dsimp [C]; positivity
  obtain ⟨m,hm⟩ := exists_nat_ge (C*H)
  refine ⟨((2:ℝ)^e+C)*R*H,by positivity,
    max 2 (ExpanderFamily.growth^(max m (10000*(e+3)))),?_⟩
  intro n hn
  have two : 2 ≤ n := le_trans (le_max_left ..) hn
  have high := Nat.le_log_of_pow_le ExpanderFamily.growth_gt_one
    (((le_max_right ..).trans hn).trans (Nat.le_succ n))
  let k := ExpanderFamily.level n
  have hk : max m (10000*(e+3)) ≤ k := high.trans (Nat.le_succ _)
  have ge : 10000*(e+3) ≤ 176*k := by omega
  have hm' : (m:ℝ) ≤ (176*k:ℕ) := by exact_mod_cast (show m ≤ 176*k by omega)
  have big := padded_scalar_expander n
  obtain ⟨lo,hi,card,_⟩ := big
  rw [card] at lo hi
  let P := 2^(176*k)
  have low : n ≤ P := (Nat.le_succ n).trans lo
  have upperNat : P ≤ 2^177*n := by
    calc
      P ≤ 2^176*(n+1) := hi
      _ ≤ 2^176*(2*n) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by rw [← Nat.mul_assoc]; rfl
  have upper : (P:ℝ) ≤ R*n := by
    simpa only [R,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using Nat.cast_le (α := ℝ) |>.mpr upperNat
  have logs : Real.log n ≤ (176*k:ℕ) := by
    calc
      Real.log n ≤ Real.log (P:ℝ) := Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
        (Nat.cast_le.mpr low)
      _ = (176*k:ℕ)*Real.log 2 := by simp only [P,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
      _ ≤ (176*k:ℕ)*1 := mul_le_mul_of_nonneg_left (by linarith only [Real.log_two_lt_d9]) (Nat.cast_nonneg _)
      _ = _ := mul_one _
  have lpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have qpos : (0:ℝ) < (176*k:ℕ) := lpos.trans_le logs
  have hR : 0 < R := pow_pos (by norm_num) _
  have base : (P:ℝ)/((176*k:ℕ)/H) ≤ R*H*n/Real.log n := by
    rw [div_div_eq_mul_div,div_le_div_iff₀ qpos lpos]
    calc
      (P:ℝ)*H*Real.log n ≤ (R*n)*H*(176*k:ℕ) :=
        mul_le_mul (mul_le_mul_of_nonneg_right upper hp.le) logs lpos.le (mul_nonneg (mul_nonneg hR.le (Nat.cast_nonneg _)) hp.le)
      _ = _ := by ring
  have bound (a : ℝ) (ha : 0 ≤ a) (le : a ≤ (2:ℝ)^e+C) :
      a*((P:ℝ)/((176*k:ℕ)/H)) ≤ (((2:ℝ)^e+C)*R*H)*n/Real.log n := by
    apply (mul_le_mul_of_nonneg_left base ha).trans
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ lpos.le
    calc
      a*(R*H*n) ≤ ((2:ℝ)^e+C)*(R*H*n) := mul_le_mul_of_nonneg_right le (mul_nonneg (mul_nonneg hR.le hp.le) (Nat.cast_nonneg _))
      _ = _ := by ring
  refine ⟨k,low,ge,(le_div_iff₀ hp).mpr (hm.trans hm'),?_,?_⟩
  · simpa only [mul_div_assoc] using bound ((2:ℝ)^e) (by positivity) (le_add_of_nonneg_right hc.le)
  · convert bound C hc.le (le_add_of_nonneg_left (by positivity)) using 1
    ring

private theorem sum_on_embedded {U V : Type} [Fintype U] [Fintype V] (j : U ↪ V)
    (f : V → ℝ) (zero : ∀ v, v ∉ Set.range j → f v = 0) :
    ∑ v, f v = ∑ u, f (j u) := by
  classical
  rw [← sum_map (f := f) (s := univ) j]
  apply (sum_subset (subset_univ _) ?_).symm
  intro v _ hv
  apply zero
  rintro ⟨u,rfl⟩
  exact hv (mem_map_of_mem j (mem_univ u))

/-- The characteristic-zero placement bounds, with orders measured on the
original graph. K and the cutoff depend only on the degree. The three bounds
use the same space, scale, placement and root for every choice of terminals. -/
theorem graph_geometry (price : PriceZero) (D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {E : Type} [Fintype E]
      (src dst : E → Fin n),
      (∀ v, (univ.filter fun t => src t = v).card + (univ.filter fun t => dst t = v).card ≤ D) →
      ∃ (X : SpectralTarget) (p : Fin n → X.carrier) (o : X.carrier) (a : ℝ), 0 < a ∧
      (∀ (w : E → ℝ) (cap : ℝ), 0 ≤ cap → (∀ edge, w edge ≤ cap) →
        ∑ edge, w edge*normalizedDist a p (src edge) (dst edge) ≤
          cap*Real.sqrt (D*n)*Real.sqrt (K*n/Real.log n)) ∧
      (∀ N (A B : Fin N ↪ Fin n), (∑ j, ∑ i, (normalizedDist a p (A i) (B j)-1)^2) ≤
        12*(N:ℝ)*(K*n/Real.log n)) ∧
      (∀ h : Fin n → ℝ, (∀ v, 0 ≤ h v) →
        (∑ v, h v*(a*dist (p v) o)) ≤ (∑ v, h v)/Real.sqrt 2 +
          Real.sqrt (∑ v, (h v)^2)*Real.sqrt (K*n/Real.log n)) := by
  classical
  let e := D+2^88
  have capD : D+2^88 ≤ 2^e := Nat.le_of_lt (Nat.lt_two_pow_self)
  obtain ⟨K,hK,n₀,padding⟩ := choose_padding e
  refine ⟨K,hK,n₀,?_⟩
  intro n hn E _ src dst degree
  obtain ⟨k,low,large,gap,edgeBudget,rootBudget⟩ := padding n hn
  let j : Fin n ↪ Fin (2^(176*k)) := Fin.castLEEmb low
  have paddedDegree (v) : (univ.filter fun t => j (src t) = v).card +
      (univ.filter fun t => j (dst t) = v).card + 2^88 ≤ 2^e := by
    by_cases h : v ∈ Set.range j
    · obtain ⟨u,rfl⟩ := h
      simpa using (Nat.add_le_add_right (degree u) (2^88)).trans capD
    · have outside (u) : j u ≠ v := fun hv => h ⟨u,hv⟩
      simpa [outside] using (Nat.le_add_left (2^88) D).trans capD
  obtain ⟨X,p,o,a,apos,_,edges,terminals,center⟩ :=
    padded_graph_geometry price k e (j ∘ src) (j ∘ dst) paddedDegree large gap
  simp only [Fintype.card_fin] at edges terminals center
  refine ⟨X,p ∘ j,o,a,apos,?_,?_,?_⟩
  · intro w cap hcap weights
    have size : Fintype.card E ≤ D*n := by
      calc
        Fintype.card E = ∑ v, (univ.filter fun t => src t = v).card :=
          card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
        _ ≤ ∑ _ : Fin n, D := sum_le_sum fun v _ => (Nat.le_add_right ..).trans (degree v)
        _ = _ := by simp [Nat.mul_comm]
    apply (edges w cap hcap weights).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast size)) hcap)
      (Real.sqrt_le_sqrt edgeBudget) (Real.sqrt_nonneg _) (mul_nonneg hcap (Real.sqrt_nonneg _))
  · intro N A B
    apply (terminals N (A.trans j) (B.trans j)).trans
    rw [mul_assoc (12*(N:ℝ))]
    exact mul_le_mul_of_nonneg_left rootBudget (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  · intro h nonneg
    let h' := Function.extend j h (fun _ => 0)
    have inside (u) : h' (j u) = h u := j.injective.extend_apply ..
    have outside (v) (hv : v ∉ Set.range j) : h' v = 0 := Function.extend_apply' _ _ _ hv
    have hnonneg (v) : 0 ≤ h' v := by
      by_cases hv : v ∈ Set.range j
      · obtain ⟨u,rfl⟩ := hv
        rw [inside]; exact nonneg _
      · rw [outside _ hv]
    have total := center h' hnonneg
    rw [sum_on_embedded j _ (fun v hv => by rw [outside v hv,zero_mul]),
      sum_on_embedded j h' outside, sum_on_embedded j _ (fun v hv => by simp [outside v hv])] at total
    simp only [inside] at total
    apply total.trans
    exact add_le_add_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt rootBudget)
      (Real.sqrt_nonneg _)) _

end OAI.Computability.MultitapeWeakETH
