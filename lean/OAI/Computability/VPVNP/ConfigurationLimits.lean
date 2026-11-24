import OAI.Computability.VPVNP.SpanningStar
import OAI.Computability.VPVNP.SpectrumCompactness
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.LiminfLimsup

/-! # Limits of scaled finite spectral configurations

The compactness step in Lemma 2.3 uses a positive lower bound on the diameter
of a normalized configuration. For a fixed set of `k ≥ 2` used parties, the
spanning-tree estimate supplies the lower bound `1 / (k - 1)`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

open Filter Set
open scoped Topology

/-- A nonzero coordinatewise limit of scaled configurations is realized by a
point of the same compact spectrum at a positive scale. The coordinates can
be the ordered pairs of a finite label set. -/
theorem exists_scaled_configuration_limit {ι K : Type*} [Fintype ι] [Nonempty ι]
    [TopologicalSpace K] {spectrum : Set K} (hcompact : IsCompact spectrum)
    (wire : K → ι → ℝ) (hwire : ∀ i, Continuous (fun k ↦ wire k i))
    {x : ℕ → K} {r : ℕ → ℝ} (hx : ∀ m, x m ∈ spectrum) (hr : ∀ m, 0 ≤ r m)
    {δ : ℝ} (hδ : 0 < δ)
    (hnorm : ∀ m, δ ≤ Finset.univ.sup' Finset.univ_nonempty (wire (x m)))
    {v : ι → ℝ} (hv : v ≠ 0)
    (hlim : ∀ i, Tendsto (fun m ↦ r m * wire (x m) i) atTop (𝓝 (v i))) :
    ∃ k ∈ spectrum, ∃ t : ℝ, 0 < t ∧ ∀ i, t * wire k i = v i := by
  classical
  let diameter (y : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty y
  have hdiam : Tendsto (fun m ↦ diameter (fun i ↦ r m * wire (x m) i)) atTop
      (𝓝 (diameter v)) :=
    Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty fun i _ ↦ hlim i
  obtain ⟨U, hU⟩ := hdiam.bddAbove_range
  have hscale (m : ℕ) : r m ∈ Icc 0 (U / δ) := by
    obtain ⟨i, hi, hiδ⟩ := (Finset.le_sup'_iff Finset.univ_nonempty).mp (hnorm m)
    refine ⟨hr m, (le_div_iff₀ hδ).2 ?_⟩
    calc
      r m * δ ≤ r m * wire (x m) i := mul_le_mul_of_nonneg_left hiδ (hr m)
      _ ≤ diameter (fun j ↦ r m * wire (x m) j) := Finset.le_sup' (fun j ↦ r m * wire (x m) j) hi
      _ ≤ U := hU ⟨m, rfl⟩
  let realize (p : K × ℝ) : ι → ℝ := fun i ↦ p.2 * wire p.1 i
  have hrealize : Continuous realize := continuous_pi fun i ↦
    continuous_snd.mul ((hwire i).comp continuous_fst)
  have hclosed : IsClosed (realize '' (spectrum ×ˢ Icc 0 (U / δ))) :=
    ((hcompact.prod isCompact_Icc).image hrealize).isClosed
  have hmem := hclosed.mem_of_tendsto (tendsto_pi_nhds.mpr hlim) <|
    Eventually.of_forall fun m ↦ ⟨(x m, r m), ⟨hx m, hscale m⟩, rfl⟩
  obtain ⟨⟨k, t⟩, ⟨hk, ht⟩, heq⟩ := hmem
  refine ⟨k, hk, t, lt_of_le_of_ne ht.1 ?_, fun i ↦ congrFun heq i⟩
  rintro rfl
  apply hv
  funext i
  simpa [realize] using congrFun heq.symm i

end Spectral

namespace WireTensor.SpectralPoint

open Filter Set
open scoped NNReal Topology

universe u v

variable {k : Type u} [Field k] {J : Type v} [Fintype J] [Nonempty J]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A nonzero coordinatewise limit of normalized configurations on fixed
parties is realized on the same parties. Labels may repeat. -/
theorem exists_wire_configuration_limit (label : ι → J) (F : ℕ → SpectralPoint k J)
    {r : ℕ → ℝ} (hr : ∀ m, 0 ≤ r m) {δ : ℝ} (hδ : 0 < δ)
    (hnorm : ∀ m, δ ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun i : ι × ι ↦ (F m).wireDistance (label i.1) (label i.2)))
    {d : ι × ι → ℝ} (hd : d ≠ 0)
    (hlim : ∀ i : ι × ι, Tendsto (fun m ↦ r m * (F m).wireDistance (label i.1) (label i.2))
      atTop (𝓝 (d i))) :
    ∃ G : SpectralPoint k J, ∃ t : ℝ, 0 < t ∧ ∀ i : ι × ι,
      t * G.wireDistance (label i.1) (label i.2) = d i := by
  let extended (g : Tensor.{u,v,0} k J → ℝ≥0) (i : ι × ι) :=
    Real.logb 2 (max 1 (g (wire (label i.1) (label i.2) (Fin 2)) : ℝ))
  have hcontinuous (i : ι × ι) : Continuous (extended · i) := by
    let W := wire (k := k) (label i.1) (label i.2) (Fin 2)
    have hW : Continuous (fun g : Tensor.{u,v,0} k J → ℝ≥0 ↦ (g W : ℝ)) :=
      NNReal.continuous_coe.comp (continuous_apply W)
    exact (continuous_const.max hW).logb
      fun _ ↦ (zero_lt_one.trans_le (le_max_left 1 _)).ne'
  have hdist (G : SpectralPoint k J) (i : ι × ι) :
      extended G.value i = G.wireDistance (label i.1) (label i.2) := by
    change Real.logb 2 (max 1 (G.wireDimension (label i.1) (label i.2) 2)) = _
    rw [max_eq_right (G.one_le_wireDimension _ _ (by decide))]
    rfl
  obtain ⟨_, ⟨G, rfl⟩, t, ht, hGt⟩ := VPVNP.Spectral.exists_scaled_configuration_limit
    (isCompact_range_value (k := k) (J := J)) extended hcontinuous
    (x := fun m ↦ (F m).value) (fun m ↦ mem_range_self (F m)) hr hδ
    (by simpa only [hdist] using hnorm) hd (by simpa only [hdist] using hlim)
  exact ⟨G, t, ht, by simpa only [hdist] using hGt⟩

/-- A matrix of labeled wire distances realized at one spectral point and one
positive common scale. -/
def Realizes (k : Type u) [Field k] {J : Type v} [Fintype J] {ι : Type*}
    (label : ι → J) (d : ι × ι → ℝ) : Prop :=
  ∃ G : SpectralPoint k J, ∃ t : ℝ, 0 < t ∧ ∀ i : ι × ι,
    t * G.wireDistance (label i.1) (label i.2) = d i

omit [Fintype ι] in
/-- After normalization on the used parties, there are finitely many label
patterns. One pattern occurs along an infinite subsequence, so its spectrum
realizes the nonzero limiting configuration. -/
theorem realizes_limit_of_finite_patterns [Finite ι] {P : Type*} [Finite P] (parties : P → Type v)
    [∀ p, Fintype (parties p)] (labels : ∀ p, ι → parties p)
    (hcover : ∀ p, Function.Surjective (labels p)) {d : ι × ι → ℝ} (hd : d ≠ 0)
    (seq : ℕ → ι × ι → ℝ) (hseq : ∃ᶠ m in atTop, ∃ p, Realizes k (labels p) (seq m))
    (hlim : ∀ i, Tendsto (fun m ↦ seq m i) atTop (𝓝 (d i))) :
    ∃ p, Realizes k (labels p) d := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨p, hp⟩ := frequently_exists.mp hseq
  obtain ⟨φ, hφ, hreal⟩ := extraction_of_frequently_atTop hp
  choose G r hr heq using hreal
  have : Nonempty (parties p) := ⟨labels p Classical.ofNonempty⟩
  have hsub (i : ι × ι) : Tendsto
      (fun m ↦ r m * (G m).wireDistance (labels p i.1) (labels p i.2)) atTop (𝓝 (d i)) :=
    ((hlim i).comp hφ.tendsto_atTop).congr fun m ↦ (heq m i).symm
  have hcard := Fintype.one_lt_card_iff_nontrivial.mpr (G 0).nontrivial_parties
  have hden : 0 < (Fintype.card (parties p) : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hcard)
  exact ⟨p, exists_wire_configuration_limit (labels p) G (fun m ↦ (hr m).le)
    (one_div_pos.mpr hden) (fun m ↦ (G m).inv_card_sub_one_le_wire_diameter _ (hcover p) hcard)
    hd hsub⟩

omit [Nonempty J] [Fintype ι] [Nonempty ι] in
/-- Repeating one party realizes the zero configuration at unit scale. -/
theorem zero_wire_configuration (G : SpectralPoint k J) (a : J) :
    ∃ label : ι → J, ∀ i : ι × ι, G.wireDistance (label i.1) (label i.2) = 0 :=
  ⟨fun _ ↦ a, fun _ ↦ G.wireDistance_self a⟩

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
