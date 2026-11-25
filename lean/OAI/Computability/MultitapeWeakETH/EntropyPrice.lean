import OAI.Computability.MultitapeWeakETH.EntropyRestriction
import OAI.Computability.MultitapeWeakETH.Grouping
import OAI.Computability.VPVNP.WireGeodesic
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalContinuity

/-! # Paired-terminal entropy comparison at spectral wire distances -/

namespace OAI.Computability.MultitapeWeakETH

open VPVNP.WireTensor Finset MatrixMultiplication MatrixMultiplication.Foundation
open LabelHierarchyCounts StageHierarchyResources ConditionalLabels Filter
open scoped BigOperators Topology Classical

private theorem stream_cost {K J P E L : Type} [Field K] [Fintype J] [Fintype P] [Nontrivial P]
    [Fintype E] [Fintype L] (F : SpectralPoint K P) (place : J → P) (root : J)
    (a b : E → J) (w : E → ℕ) (u v : L → J) (bits : L → ℕ) (r : ℕ)
    (Stream : J → Type) [∀ j, Fintype (Stream j)] (pos : ∀ j, 0 < Fintype.card (Stream j))
    (h : Restricts (tensorProduct (tensorFamilyProduct (fun _ : Fin r =>
        wireNetwork (k := K) a b (fun e => Fin (2^w e)))) (wireNetwork (fun _ : J => root) id Stream))
      (wireNetwork u v (fun j => Fin (2^bits j)))) :
    ∑ l, (bits l : ℝ)*F.wireDistance (place (u l)) (place (v l)) ≤
      r*(∑ e, (w e : ℝ)*F.wireDistance (place (a e)) (place (b e))) +
        ∑ j, Real.logb 2 (Fintype.card (Stream j))*F.wireDistance (place root) (place j) := by
  let S := ∑ e, (w e : ℝ)*F.wireDistance (place (a e)) (place (b e))
  have mono := NNReal.coe_le_coe.mpr (F.monotone (group_restricts place h))
  rw [value_group_product,value_group_family,prod_const,card_univ,Fintype.card_fin,
    value_group_wires,value_group_wires,value_group_wires,
    NNReal.coe_mul,NNReal.coe_pow,F.value_binary_wireNetwork,F.value_binary_wireNetwork,
    F.value_wireNetwork_eq_prod_rpow _ _ _ pos] at mono
  have spoke (j : J) : (Fintype.card (Stream j):ℝ)^F.wireDistance (place root) (place (id j)) =
      (2:ℝ)^(Real.logb 2 (Fintype.card (Stream j))*F.wireDistance (place root) (place j)) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_logb (by norm_num) (by norm_num)
      (Nat.cast_pos.mpr (pos j))]
    rfl
  simp only [Function.comp_apply] at mono
  simp_rw [spoke] at mono
  rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2),← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 2)] at mono
  rw [mul_comm _ (r:ℝ)] at mono
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp mono

private theorem pin_rate {A B : Type} [Fintype A] [Fintype B] (counts : A → ℕ)
    (pos : 0 < ∑ a, counts a) (f : A → B) :
    let D := ∑ a, counts a
    let q := pushforwardCounts counts f
    Tendsto (fun t : ℕ => Real.logb 2 (Fintype.card
        (PopulationWords (Fin (t*D)) (fun b => t*q b))) / (t*D:ℕ)) atTop
      (𝓝 (finiteEntropy (((normalizedCountLaw counts pos).map f).mass) / Real.log 2)) := by
  intro D q
  have total : ∑ b, q b = D := pushforwardCounts_sum counts f
  have rate := (tendsto_log_multinomial_mul q (total ▸ pos)).div_const (Real.log 2)
  have prob (b) : ((normalizedCountLaw counts pos).map f).mass b = (q b:ℝ)/D := by
    simp only [FiniteLaw.map_mass,normalizedCountLaw_mass,q,pushforwardCounts,Nat.cast_sum,Finset.sum_div]
    apply sum_congr rfl
    intro x _
    by_cases h : f x = b <;> simp [h,D]
  rw [total,show (fun b => (q b:ℝ)/D) = _ from (funext prob).symm] at rate
  apply rate.congr
  intro t
  rw [populationWords_card,Real.logb,Nat.cast_mul]
  · ring
  · simp only [Fintype.card_fin,← mul_sum,total]



variable {K J P E A : Type} [Field K] [Fintype J] [Fintype P] [Nontrivial P] [Fintype E] [Fintype A]

/-- The spectral price of an exact-type source in terms of the actual
conditional information exposed by its successive binary coordinates. -/
theorem paired_entropy_counts (F : SpectralPoint K P) (place : J → P) (root : J) (a b : E → J) (w : E → ℕ)
    (Pin : J → Type) [∀ j, Fintype (Pin j)] (pin : ∀ j, A → Pin j)
    (counts : A → ℕ) (positive : 0 < ∑ x, counts x) (labels : ℕ → A → Bool) (depth : ℕ)
    (separate : Function.Injective (labelRecordOf labels depth)) (u v : Fin depth → J)
    (maps : ∀ j, Pin j → (wireNetwork (k := K) u v (fun _ => Bool)).Basis j →
      (wireNetwork (k := K) a b (fun e => Fin (2^w e))).Basis j → K)
    (scalar : A → K) (nz : ∀ x, scalar x ≠ 0)
    (display : ∀ x, applyLocal (fun j => maps j (pin j x))
      (wireNetwork a b (fun e => Fin (2^w e))).coeff =
      fun z => if z = edgeAssignment u v (fun j => labels j x) then scalar x else 0) :
    let p := normalizedCountLaw counts positive
    (∑ l : Fin depth, (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy l /
      Real.log 2 * F.wireDistance (place (u l)) (place (v l))) ≤
      ∑ e, (w e:ℝ)*F.wireDistance (place (a e)) (place (b e)) +
        ∑ j, finiteEntropy ((p.map (pin j)).mass)/Real.log 2 * F.wireDistance (place root) (place j) := by
  intro p
  let D := ∑ x, counts x
  let r (t : ℕ) := t*D
  let T := wireNetwork (k := K) a b (fun e => Fin (2^w e))
  let bits (t : ℕ) (l : Fin depth) := colorBits (stageRefinementCount counts labels l t) (r t)
  let Stream (t : ℕ) (j : J) :=
    PopulationWords (Fin (r t)) (fun q => t*pushforwardCounts counts (pin j) q)
  have grow : Tendsto r atTop atTop := tendsto_atTop_mono
    (fun t => Nat.le_mul_of_pos_right t positive) tendsto_id
  have given (l : Fin depth) : Tendsto (fun t => (bits t l:ℝ)/(r t:ℝ)) atTop
      (𝓝 ((FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy l / Real.log 2)) := by
    apply colorBits_rate grow
    simpa only [r,D,Nat.cast_mul] using extension_entropy_limit counts positive labels depth l
  have paid (j : J) := pin_rate counts positive (pin j)
  apply le_of_tendsto_of_tendsto
    (tendsto_finsetSum univ fun l _ => (given l).mul_const (F.wireDistance (place (u l)) (place (v l))))
    (tendsto_const_nhds.add (tendsto_finsetSum univ fun j _ =>
      (paid j).mul_const (F.wireDistance (place root) (place j))))
  filter_upwards [grow.eventually_gt_atTop (depth+1)] with t ht
  have card (j : J) : Fintype.card (Stream t j) =
      Nat.multinomial univ (fun q => t*pushforwardCounts counts (pin j) q) :=
    populationWords_card _ (by simp [r,D,← mul_sum,pushforwardCounts_sum])
  have restriction := exact_type_wire_restriction T root Pin pin counts labels depth t separate ht u v
    maps scalar nz display
  have h := stream_cost F place root a b w u v (bits t) (r t) (Stream t)
    (fun j => (card j) ▸ Nat.multinomial_pos _ _) restriction
  have pos : (0:ℝ) < r t := Nat.cast_pos.mpr (by omega)
  have hdiv := div_le_div_of_nonneg_right h pos.le
  rw [add_div,mul_div_cancel_left₀ _ pos.ne',sum_div,sum_div] at hdiv
  convert hdiv using 1 <;> apply_rules [congrArg₂ (· + ·), sum_congr rfl, Eq.refl] <;>
    intros <;> dsimp only [D,r,Stream] <;> ring

private theorem law_eq_of_mass (p q : FiniteLaw A) (h : p.mass = q.mass) : p = q := by
  cases p
  cases q
  congr

/-- The paired-terminal entropy inequality for every finite source law on
its possible payloads. Bit labels may be exposed in any separating order.
The distances are those of one common spectral point. -/
theorem paired_entropy (F : SpectralPoint K P) (place : J → P) (root : J) (a b : E → J) (w : E → ℕ)
    (Pin : J → Type) [∀ j, Fintype (Pin j)] (pin : ∀ j, A → Pin j)
    (p : FiniteLaw A) (labels : ℕ → A → Bool) (depth : ℕ)
    (separate : Function.Injective (labelRecordOf labels depth)) (u v : Fin depth → J)
    (maps : ∀ j, Pin j → (wireNetwork (k := K) u v (fun _ => Bool)).Basis j →
      (wireNetwork (k := K) a b (fun e => Fin (2^w e))).Basis j → K)
    (scalar : A → K) (nz : ∀ x, scalar x ≠ 0)
    (display : ∀ x, applyLocal (fun j => maps j (pin j x))
      (wireNetwork a b (fun e => Fin (2^w e))).coeff =
      fun z => if z = edgeAssignment u v (fun j => labels j x) then scalar x else 0) :
    (∑ l : Fin depth, (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy l /
      Real.log 2 * F.wireDistance (place (u l)) (place (v l))) ≤
      ∑ e, (w e:ℝ)*F.wireDistance (place (a e)) (place (b e)) +
        ∑ j, finiteEntropy ((p.map (pin j)).mass)/Real.log 2 * F.wireDistance (place root) (place j) := by
  classical
  obtain ⟨q,close⟩ := exists_rational_law_sequence p
  have cond (l : Fin depth) :
      Tendsto (fun t => (FiniteLabelHierarchy.ofLawLabels (q t).toFiniteLaw labels depth).refinementEntropy l)
        atTop (𝓝 ((FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy l)) := by
    simp only [refinementEntropy_eq_prefix_difference _ labels depth l l.isLt]
    exact (tendsto_map_entropy close (labelRecordOf labels (l.val+1))).sub
      (tendsto_map_entropy close (labelRecordOf labels l.val))
  apply le_of_tendsto_of_tendsto
    (tendsto_finsetSum univ fun l _ => ((cond l).div_const (Real.log 2)).mul_const (F.wireDistance (place (u l)) (place (v l))))
    (tendsto_const_nhds.add (tendsto_finsetSum univ fun j _ =>
      ((tendsto_map_entropy close (pin j)).div_const (Real.log 2)).mul_const (F.wireDistance (place root) (place j))))
  filter_upwards with t
  obtain ⟨counts,pos,mass,_⟩ := (q t).exists_exactWords_entropy_limit
  have equal : normalizedCountLaw counts pos = (q t).toFiniteLaw :=
    law_eq_of_mass _ _ (funext mass)
  have bound := paired_entropy_counts F place root a b w Pin pin counts pos labels depth separate u v
    maps scalar nz display
  dsimp only at bound
  rw [equal] at bound
  exact bound

/-- Lemma 3.2 on a finite network with a distinguished root site. Its
placement includes the root, which may be an isolated vertex. Marginal
entropies are charged per vertex, even for coinciding placed vertices. -/
theorem paired_entropy_at_placement {X : Type} [PseudoMetricSpace X]
    (realizable : VPVNP.WireGeometry.RealizableConfigurations K X) (place : J → X) (root : J) (a b : E → J) (w : E → ℕ)
    (Pin : J → Type) [∀ j, Fintype (Pin j)] (pin : ∀ j, A → Pin j)
    (p : FiniteLaw A) (labels : ℕ → A → Bool) (depth : ℕ)
    (separate : Function.Injective (labelRecordOf labels depth)) (u v : Fin depth → J)
    (maps : ∀ j, Pin j → (wireNetwork (k := K) u v (fun _ => Bool)).Basis j →
      (wireNetwork (k := K) a b (fun e => Fin (2^w e))).Basis j → K)
    (scalar : A → K) (nz : ∀ x, scalar x ≠ 0)
    (display : ∀ x, applyLocal (fun j => maps j (pin j x))
      (wireNetwork a b (fun e => Fin (2^w e))).coeff =
      fun z => if z = edgeAssignment u v (fun j => labels j x) then scalar x else 0) :
    (∑ l : Fin depth, (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy l /
      Real.log 2 * dist (place (u l)) (place (v l))) ≤
      ∑ e, (w e:ℝ)*dist (place (a e)) (place (b e)) +
        ∑ j, finiteEntropy ((p.map (pin j)).mass)/Real.log 2 * dist (place root) (place j) := by
  classical
  let e := Fintype.equivFin J
  obtain ⟨W⟩ := realizable (Fintype.card J) (place ∘ e.symm)
  let loc (j : J) := W.label (e j)
  have distance (i j : J) : dist (place i) (place j) = W.scale * W.spectrum.wireDistance (loc i) (loc j) := by
    simpa only [Function.comp_apply,Equiv.symm_apply_apply,loc] using W.distances (e i) (e j)
  have h := paired_entropy W.spectrum loc root a b w Pin pin p labels depth separate u v maps scalar nz display
  have scaled := mul_le_mul_of_nonneg_left h W.scale_pos.le
  simp_rw [distance,mul_left_comm _ W.scale _,← mul_sum,← mul_add]
  exact scaled

end OAI.Computability.MultitapeWeakETH
