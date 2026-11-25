import OAI.Hierarchy.FlatFieldExtension
import OAI.Hierarchy.IntegralRestriction

namespace OAI
/-! # Field transfer of Euclidean spectral flats

A limit of the spectra over large prime fields gives a homomorphism on integral
tensors. Good reduction makes it respect all comparisons over the target field.
Spectral extension then provides a single point over that field, with every
binary wire retaining its prescribed length. -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open Filter Set Topology
open scoped NNReal

namespace WireChart

variable {J : Type} [Fintype J] [Nontrivial J]

private noncomputable abbrev wire (K : Type*) [CommSemiring K] (i j : J) : TensorClass.{0} J K :=
  ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![i,j])

private theorem map_wire (K : Type*) [Field K] (i j : J) :
    mapScalars (Int.castRingHom K) (wire ℤ i j) = wire K i j := by
  classical
  let h := Int.castRingHom K
  have eqn : ((Raw.diagonal (Fin 2) ℤ (Fin 2)).group ![i,j]).mapScalars h =
      (Raw.diagonal (Fin 2) K (Fin 2)).group ![i,j] := by
    unfold Raw.group Raw.diagonal Raw.mapScalars
    congr 1
    funext x
    dsimp only
    simp only [map_sum, apply_ite h, map_one, map_zero]
    all_goals
      apply Finset.sum_congr rfl
      intro d _
      split <;> rfl
  exact congrArg ofRaw eqn

private theorem coordinate_bound (X : TensorClass.{0} J ℤ) :
    ∃ B : ℝ≥0, ∀ (K : Type) [Field K]
      (φ : normalizedSpectrum (S := TensorClass.{0} J K) (· ≤ ·)),
      (pullbackSpectrum (Int.castRingHom K) φ).val X ≤ B := by
  classical
  induction X using Quotient.inductionOn with
  | _ T =>
    refine ⟨Fintype.card (∀ i, T.Leg i),fun K _ φ => ?_⟩
    let U := T.mapScalars (Int.castRingHom K)
    have hle : ofRaw U ≤ (Fintype.card (∀ i, U.Leg i) : TensorClass.{0} J K) := by
      simpa only [ofRaw_diagonal_eq_natCast, Fintype.card_ulift, Fintype.card_fin] using
        (ofRaw_le_iff.mpr (U.restricts_diagonal J))
    exact (φ.property.2.2.2.2 _ _ hle).trans_eq
      (map_natCast (normalizedSpectrum.toRingHom φ) _)

private theorem compact_limit {A : Type*} [TopologicalSpace A] (u : Ultrafilter ℕ)
    (f : ℕ → A) {C : Set A} (hc : IsCompact C) (h : ∀ i, f i ∈ C) :
    ∃ x ∈ C, Tendsto f (u : Filter ℕ) (𝓝 x) := by
  exact hc.ultrafilter_le_nhds' (u.map f) (Filter.Eventually.of_forall h : ∀ᶠ i in (u : Filter ℕ), f i ∈ C)

omit [Nontrivial J] in
private theorem scale_upper {K Y : Type*} [Field K] [MetricSpace Y]
    (P : SpectralPlacementPrices K Y) (e : J ↪ Y) (i : J) :
    P.price (Raw.diagonal J K (Fin 2)) e ≤ ∑ j, dist (e j) (e i) := by
  have h := P.transport (Raw.diagonal J K (Fin 2)) e (fun _ => e i)
  rw [P.collapsed, Real.dist_eq, sub_zero] at h
  have logtwo : Real.logb 2 2 = 1 := Real.logb_self_eq_one (by norm_num)
  apply (le_abs_self _).trans
  simpa [Raw.diagonal, logtwo] using h

/-- The joint limit on integral tensors respects every restriction after passing
to a characteristic-zero field. In particular the same scale works on every wire. -/
theorem of_prime_fields_charZero (F : Type*) [Field F] [CharZero F]
    {Y : Type*} [MetricSpace Y] [Nonempty Y]
    (P : ∀ (p : ℕ) [Fact p.Prime], SpectralPlacementPrices (ZMod p) Y) :
    Nonempty (SpectralPlacementPrices F Y) := by
  classical
  apply prices_of_charts
  intro I _ _ e
  choose p large prime using Nat.exists_infinite_primes
  let (n : ℕ) : Fact (p n).Prime := ⟨prime n⟩
  let c (n : ℕ) := (P (p n)).price (Raw.diagonal I (ZMod (p n)) (Fin 2)) e
  choose φ distances using fun n : ℕ => of_prices (P (p n)) e
  let g (n : ℕ) := pullbackSpectrum (Int.castRingHom (ZMod (p n))) (φ n)
  let u := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨a,b,hab⟩ := exists_pair_ne I
  obtain ⟨c₀,hc₀,hc⟩ := compact_limit u c
    (isCompact_Icc (a := dist (e a) (e b)) (b := ∑ i, dist (e i) (e a)))
    (fun n => ⟨(P (p n)).dist_le_diagonal e a b,scale_upper (P (p n)) e a⟩)
  have hpos : 0 < c₀ := (dist_pos.mpr (e.injective.ne hab)).trans_le hc₀.1
  have limit (x : TensorClass.{0} I ℤ) :
      ∃ w : ℝ≥0, Tendsto (fun n => (g n).val x) (u : Filter ℕ) (𝓝 w) := by
    obtain ⟨B,hB⟩ := coordinate_bound x
    obtain ⟨w,_,hw⟩ := compact_limit u _ (isCompact_Icc (a := 0) (b := B))
      (fun n => ⟨bot_le,hB (ZMod (p n)) (φ n)⟩)
    exact ⟨w,hw⟩
  choose w hw using limit
  have wmem : w ∈ normalizedSpectrum (S := TensorClass.{0} I ℤ) (· ≤ ·) :=
    (isClosed_normalizedSpectrum _).mem_of_tendsto (tendsto_pi_nhds.mpr hw)
      (Eventually.of_forall fun n => (g n).property)
  let f := normalizedSpectrum.toRingHom ⟨w,wmem⟩
  obtain ⟨ψ,hψ⟩ := exists_spectrum_extension (mapScalars (I := I) (Int.castRingHom F)) f
    (fun x y xy => by
      obtain ⟨N,hN⟩ := IntegralRestriction.eventually_mono F x y xy
      apply le_of_tendsto_of_tendsto (hw x) (hw y)
      apply Filter.Eventually.filter_mono (Ultrafilter.of_le atTop)
      filter_upwards [eventually_ge_atTop N] with n hn
      exact hN (p n) (hn.trans (large n)) (φ n))
    isCompact_spectrum (strictSpectralComparison I F)
  refine ⟨ψ,c₀,hpos,fun i j => ?_⟩
  let x := wire ℤ i j
  have wire_limit : Tendsto (fun n => (φ n).val (wire (ZMod (p n)) i j))
      (u : Filter ℕ) (𝓝 (ψ.val (wire F i j))) := by
    rw [← map_wire F i j, hψ]
    rw [show f (wire ℤ i j) = w (wire ℤ i j) from rfl]
    simpa only [x, g, pullbackSpectrum_apply, map_wire] using hw x
  have hn n : 1 ≤ (φ n).val (wire (ZMod (p n)) i j) := by
    apply one_le_raw_spectralValue
    exact (Raw.group_ne_zero_iff _ _).mpr (wire_ne_zero _)
  have one := ge_of_tendsto' wire_limit hn
  have hp : (ψ.val (wire F i j) : ℝ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le one).ne'
  have identity := hc.mul ((NNReal.continuous_coe.tendsto _).comp wire_limit |>.logb hp (b := 2))
  apply tendsto_nhds_unique identity
  exact tendsto_const_nhds.congr (fun n => (distances n i j).symm)

end WireChart

/-- Field transfer for spectral flats. Spectral flats in every finite prime
field suffice for the same dimension over an arbitrary coefficient field. -/
theorem HasSpectralFlat.of_prime_fields {d : ℕ}
    (prime : ∀ (p : ℕ) [Fact p.Prime], HasSpectralFlat (ZMod p) d)
    (F : Type*) [Field F] : HasSpectralFlat F d := by
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hp | hz
  · let : Fact (ringChar F).Prime := ⟨hp⟩
    exact of_prime_characteristic F (prime (ringChar F))
  · let : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hz
    exact WireChart.of_prime_fields_charZero F (fun p _ => (prime p).some)


end Hierarchy

end OAI
