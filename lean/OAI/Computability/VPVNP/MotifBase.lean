import OAI.Computability.VPVNP.TensorSpectralComparison
import OAI.Computability.VPVNP.MotifWirePowers
import OAI.Computability.VPVNP.MotifOrdinarySum
import OAI.Computability.VPVNP.MotifSupplyEnergy
import OAI.Computability.VPVNP.MotifWidths

/-!
# Fixed base identities for wire motifs

In Theorem 6.1, a finite supply grid beats each demand grid point at every
spectral point. The supply witness may depend on the spectral point.
Taking the direct sum of the supply grid and applying strict comparison
yields one copy bound for all powers. Distributing the powers yields actual
ordinary sums of local maps. Each summand is indexed by one copy and an
ordered list of grid points, with widths added edge by edge.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifBase

open WireTensor WireTensor.RestrictionClass

universe u v
variable {k : Type u} {J : Type v} [Field k] [Fintype J] [Nontrivial J]
variable {D S : Type} [Fintype D] [Fintype S] {W Z : Type*} [Fintype W] [Finite Z]

/-- The ordinary tensor of binary equality wires with a given integer width profile. -/
noncomputable abbrev binaryWires {k : Type u} [CommSemiring k] {E : Type} [Fintype E]
    (a b : E → J) (width : E → ℕ) :
    Tensor.{u,v,0} k J := wireNetwork a b (fun e ↦ Fin (2 ^ width e))

/-- The supply widths of a selector are the totals of the selected grid profiles. -/
def payload {h : ℕ} (w : W → S → ℕ) (σ : Fin h → W) (e : S) : ℕ := ∑ i, w (σ i) e

/-- The base identity (6.2) before grouping repeated copies by payload. -/
def BaseIdentity (k : Type u) [CommSemiring k] {J : Type v} [Fintype J]
    (a b : D → J) (c d : S → J) (z : D → ℕ) (w : W → S → ℕ) (K h : ℕ) : Prop :=
  let X := binaryWires (k := k) a b (fun e ↦ h * z e)
  let T (σ : Fin K × (Fin h → W)) := binaryWires (k := k) c d (payload w σ.2)
  ∃ L : ∀ σ j, X.Basis j → (T σ).Basis j → k, X.coeff = ∑ σ, applyLocal (L σ) (T σ).coeff

/-- The supply profile in the strict width comparison can vary with the spectral point. -/
def StrictAtSpectrum (k : Type u) [Field k] {J : Type v} [Fintype J]
    (a b : D → J) (c d : S → J) (z : D → ℕ) (w : W → S → ℕ) : Prop :=
  ∀ F : SpectralPoint k J, ∃ i : W,
    (∑ e, (z e : ℝ) * F.wireDistance (a e) (b e)) <
      ∑ e, (w i e : ℝ) * F.wireDistance (c e) (d e)

private theorem selector_expansion {A : Type*} [CommSemiring A] (y : W → A) (K h : ℕ) :
    (K : A) * (∑ i, y i) ^ h =
      ∑ σ : Fin K × (Fin h → W), ∏ j, y (σ.2 j) := by
  rw [Fintype.sum_pow, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem copy_bound (a b : D → J) (c d : S → J) (z : D → ℕ) (w : W → S → ℕ)
    (hs : StrictAtSpectrum k a b c d z w) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ h : ℕ,
      binaryNetworkClass (k := k) a b z ^ h ≤
        (K : RestrictionClass k J) * (∑ i, binaryNetworkClass c d (w i)) ^ h := by
  classical
  let a₀ := Classical.choice (inferInstance : Nonempty J)
  let rank := flatteningRankHom (k := k) a₀
  let : CharZero (RestrictionClass k J) := rank.charZero
  let X := binaryNetworkClass (k := k) a b z
  let Y : RestrictionClass k J := ∑ i, binaryNetworkClass c d (w i)
  have comp (f : RestrictionClass k J →+* ℝ) (hf : Monotone f) : f X < f Y := by
    let F := toSpectralPoint f hf
    obtain ⟨i, hi⟩ := hs F
    have h₁ : f X < f (binaryNetworkClass c d (w i)) := by
      change (F.value (binaryWires a b z) : ℝ) < (F.value (binaryWires c d (w i)) : ℝ)
      rw [F.value_binary_wireNetwork, F.value_binary_wireNetwork]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hi
    change _ < f (∑ j, binaryNetworkClass c d (w j))
    rw [map_sum]
    exact h₁.trans_le (Finset.single_le_sum
      (fun j _ ↦ by simpa using hf (orderBounds.zero_le (binaryNetworkClass c d (w j))))
      (Finset.mem_univ i))
  have hy : Y ≠ 0 := by
    intro hY
    let F := flatteningPoint (k := k) a₀
    have hm := ofSpectralPoint_monotone F
    have hx := comp (ofSpectralPoint F) hm
    rw [hY, map_zero] at hx
    exact hx.not_ge (by simpa using hm (orderBounds.zero_le X))
  exact Spectral.strict_spectral_comparison orderBounds rank (flatteningRankHom_monotone a₀) hy comp

private theorem baseIdentity_of_bound (a b : D → J) (c d : S → J) (z : D → ℕ) (w : W → S → ℕ)
    {K h : ℕ} (bound : binaryNetworkClass (k := k) a b z ^ h ≤
      (K : RestrictionClass k J) * (∑ i, binaryNetworkClass c d (w i)) ^ h) :
    BaseIdentity k a b c d z w K h := by
  classical
  apply ordinary_sum_of_class_le
  change binaryNetworkClass (k := k) a b (fun e ↦ h * z e) ≤
    ∑ σ : Fin K × (Fin h → W), binaryNetworkClass c d (payload w σ.2)
  rw [binaryNetworkClass_pow]
  rw [selector_expansion] at bound
  have term (σ : Fin K × (Fin h → W)) :
      binaryNetworkClass (k := k) c d (payload w σ.2) =
        ∏ j, binaryNetworkClass c d (w (σ.2 j)) :=
    binaryNetworkClass_sum c d Finset.univ (fun j ↦ w (σ.2 j))
  simp_rw [term]
  exact bound

private theorem cast_mono {n m : ℕ} (h : n ≤ m) :
    (n : RestrictionClass k J) ≤ (m : RestrictionClass k J) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa only [Nat.cast_add, add_zero] using
    orderBounds.add_mono (le_refl (n : RestrictionClass k J)) (orderBounds.zero_le (r : _))

/-- A single copy count gives base identities for every demand profile in a
finite grid and every power, over the specified field. -/
theorem uniform_base_identity (a b : D → J) (c d : S → J) (z : Z → D → ℕ) (w : W → S → ℕ)
    (hs : ∀ j, StrictAtSpectrum k a b c d (z j) w) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ j h, BaseIdentity k a b c d (z j) w K h := by
  classical
  let := Fintype.ofFinite Z
  choose K _ hbound using fun j ↦ copy_bound a b c d (z j) w (hs j)
  let N := (∑ j, K j) + 1
  refine ⟨N, Nat.le_add_left _ _, fun j h ↦ baseIdentity_of_bound _ _ _ _ _ _ ?_⟩
  have hj : K j ≤ N := (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (K i))
    (Finset.mem_univ j)).trans (Nat.le_succ _)
  apply (hbound j h).trans
  simpa only [mul_comm] using
    orderBounds.mul_mono ((∑ i, binaryNetworkClass (k := k) c d (w i)) ^ h) (cast_mono hj)

open MotifGrid

variable {p : D → ℝ} {q : S → ℝ} {H R : ℝ}

/-- The weighted comparison (6.1) gives a simultaneous base identity on the
integer width grid at every positive denominator multiple. -/
theorem connected_grid_base_identity (G : StrictGrids p q H R) (a b : D → J)
    (P : MotifSelector.Supply J S) (hq : ∀ e, 0 < q e)
    (hcomp : ∀ F : SpectralPoint k J, distanceEnergy p (fun i ↦ F.wireDistance (a i) (b i)) ≤
      H * distanceEnergy q (fun i ↦ F.wireDistance (P.src i) (P.dst i)))
    {t : ℕ} (ht : 0 < t) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (z : G.demands) h, BaseIdentity k a b P.src P.dst
      (G.demandWidths t z) (G.supplyWidths t) K h := by
  apply uniform_base_identity
  intro z F
  exact G.integer_strict ht z _ _ (fun e ↦ F.wireDistance_nonneg _ _)
    (F.connected_distanceEnergy_pos P.src P.dst P.color_eq_of_connected q hq) (hcomp F)

/-- Choosing the denominator multiple before the tensor power makes the
selector fraction as small as prescribed. The same base identity works for
all rounded demand profiles and bounds the norm of every selector's payload. -/
theorem exists_base_block (G : StrictGrids p q H R) (a b : D → J)
    (P : MotifSelector.Supply J S) (hq : ∀ e, 0 < q e)
    (hcomp : ∀ F : SpectralPoint k J, distanceEnergy p (fun i ↦ F.wireDistance (a i) (b i)) ≤
      H * distanceEnergy q (fun i ↦ F.wireDistance (P.src i) (P.dst i)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (t h K : ℕ), 0 < t ∧ 0 < h ∧ 1 ≤ K ∧
      (MotifWidths.selectorBits K G.supplies.card h : ℝ) / (h * (t * G.denominator) : ℝ) < δ ∧
      (∀ z : G.demands, BaseIdentity k a b P.src P.dst
        (G.demandWidths t z) (G.supplyWidths t) K h) ∧
      ∀ σ : Fin h → G.supplies, widthNorm q (fun e ↦ (payload (G.supplyWidths t) σ e : ℝ)) ≤
        (h * (t * G.denominator) : ℕ) * R := by
  classical
  have atScale (t : ℕ) : ∃ K : ℕ, 1 ≤ K ∧ (0 < t → ∀ (z : G.demands) h,
      BaseIdentity k a b P.src P.dst (G.demandWidths t z) (G.supplyWidths t) K h) := by
    by_cases ht : 0 < t
    · obtain ⟨K, hK, hbase⟩ := connected_grid_base_identity G a b P hq hcomp ht
      exact ⟨K, hK, fun _ ↦ hbase⟩
    · exact ⟨1, le_rfl, fun h ↦ (ht h).elim⟩
  choose K hK hbase using atScale
  obtain ⟨t, h, ht, hh, hover⟩ := MotifWidths.exists_selector_block G.denominator
    G.supplies.card G.denominator_pos K hδ
  exact ⟨t, h, K t, ht, hh, hK t, hover, fun z ↦ hbase t ht z h,
    MotifWidths.base_payload_bound G hq t h⟩

end MotifBase

end VPVNP
end Computability
end OAI
