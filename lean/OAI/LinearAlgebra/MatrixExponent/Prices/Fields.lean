import OAI.LinearAlgebra.MatrixExponent.Prices.Space
import OAI.LinearAlgebra.MatrixExponent.Spectral.Placements
import OAI.LinearAlgebra.MatrixExponent.Spectrum.Extension
import OAI.LinearAlgebra.TensorSpectrum.TagGrowth
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometrySector
import OAI.LinearAlgebra.MatrixExponent.Spectral.Transport

/-!
# Normalization after changing the marked sites

Placement preserves products but may lose additivity. Its action on
full diagonals determines an exponent. Taking the inverse power restores
additivity, as the binomial expansion has only linearly many types.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S T : Type} [Field K] [Fintype S] [Fintype T]

theorem ordinary_mono {D E : ℝ} (h : D ≤ E) : ordinary K S D ⊆ ordinary K S E := by
  rintro P ⟨d, ⟨hd, hd'⟩, f, hf, rfl⟩
  exact ⟨d, ⟨hd, hd'.trans h⟩, f, hf, rfl⟩

private theorem linear_loss {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, a ^ n ≤ (n + 1 : ℝ) * b ^ n) : a ≤ b :=
  TensorSpectrum.le_of_pow_le_polynomial_mul_pow b a 1 1 hb ha zero_lt_one zero_le_one
    (fun n _ => by simpa only [Real.rpow_one, one_mul] using h n)

theorem normalize_hom {R : Type*} [CommSemiring R] [PartialOrder R]
    (hadd : ∀ x y z : R, x ≤ y → x + z ≤ y + z) (hz0 : ∀ x : R, 0 ≤ x)
    (g : R →* ℝ)
    (hm : Monotone g) (hz : g 0 = 0) (ha : ∀ a b, g (a + b) ≤ g a + g b)
    {p : ℝ} (hp : 0 < p) (hn : ∀ n : ℕ, g n = (n : ℝ) ^ p) :
    ∃ f : R →+* ℝ, Monotone f ∧ ∀ a, f a = g a ^ p⁻¹ := by
  have h0 (a) : 0 ≤ g a := hz ▸ hm (hz0 a)
  let j : R →* ℝ :=
    { toFun := fun a => g a ^ p⁻¹
      map_one' := by rw [map_one, Real.one_rpow]
      map_mul' := fun a b => by rw [g.map_mul, Real.mul_rpow (h0 a) (h0 b)] }
  have j0 (a) : 0 ≤ j a := Real.rpow_nonneg (h0 a) _
  have jm : Monotone j := fun a _ h =>
    Real.rpow_le_rpow (h0 a) (hm h) (inv_nonneg.mpr hp.le)
  have jn (n : ℕ) : j n = (n : ℝ) := by
    change g n ^ p⁻¹ = _
    rw [hn, Real.rpow_rpow_inv (Nat.cast_nonneg _) hp.ne']
  have sum_le (U : Finset ℕ) (A : ℕ → R) :
      g (∑ i ∈ U, A i) ≤ ∑ i ∈ U, g (A i) := by
    induction U using Finset.induction_on with
    | empty => simp [hz]
    | insert i U hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (ha _ _).trans (add_le_add le_rfl ih)
  have ja (x y : R) : j (x + y) = j x + j y := by
    let A (n i : ℕ) := x ^ i * y ^ (n - i) * (n.choose i : R)
    let U (n : ℕ) := Finset.range (n + 1)
    have e (n : ℕ) : (x + y) ^ n = ∑ i ∈ U n, A n i := add_pow x y n
    have e' (n : ℕ) : (j x + j y) ^ n = ∑ i ∈ U n, j (A n i) := by
      simp only [A, U, j.map_mul, map_pow, jn, add_pow]
    have hs := add_nonneg (j0 x) (j0 y)
    apply le_antisymm
    · apply (Real.rpow_inv_le_iff_of_pos (h0 _) hs hp).mpr
      apply linear_loss (h0 _) (Real.rpow_nonneg hs _)
      intro n
      rw [← map_pow, e, Real.rpow_pow_comm hs]
      refine (sum_le _ _).trans ?_
      have hl (i : ℕ) (hi : i ∈ U n) : g (A n i) ≤ ((j x + j y) ^ n) ^ p := by
        apply (Real.rpow_inv_le_iff_of_pos (h0 _) (pow_nonneg hs n) hp).mp
        change j (A n i) ≤ _
        rw [e']
        exact Finset.single_le_sum (fun i _ => j0 (A n i)) hi
      simpa [U, nsmul_eq_mul] using Finset.sum_le_card_nsmul (U n) _ _ hl
    · apply linear_loss hs (j0 _)
      intro n
      rw [e', ← map_pow, e]
      have hl (i : ℕ) (hi : i ∈ U n) : j (A n i) ≤ j (∑ t ∈ U n, A n t) := by
        apply jm
        rw [← Finset.add_sum_erase (U n) (A n) hi, add_comm]
        exact (zero_add _).symm.trans_le (hadd 0 _ (A n i) (hz0 _))
      simpa [U, nsmul_eq_mul] using Finset.sum_le_card_nsmul (U n) _ _ hl
  exact ⟨{ j with map_add' := ja, map_zero' := by simpa using jn 0 }, jm, fun _ => rfl⟩

open scoped NNReal in
theorem zero_ordinary [Nontrivial S] {D : ℝ} (hD : 0 ≤ D) :
    (0 : Tensor K S → ℝ) ∈ ordinary K S D := by
  have h (a b : ℕ) (hab : (a : Tensor K S) ≤ b) : (a : ℝ≥0) ≤ b :=
    Nat.cast_le.mpr ((natCast_le_iff _ _).mp hab)
  obtain ⟨g, hg, _⟩ := Spectrum.extension add_le_add_right mul_le_mul_left zero_le
    one_le exists_bound (Nat.castRingHom (Tensor K S)) (Nat.castRingHom ℝ≥0) h
  exact ⟨0, ⟨le_rfl, hD⟩, NNReal.toRealHom.comp g, hg, funext fun _ => (zero_mul _).symm⟩

variable [DecidableEq S] [DecidableEq T]

private theorem diagonal_cost [Nonempty S] (x : S → T) (c : S)
    (f : Tensor K T →+* ℝ) (hf : Monotone f) :
    Real.log (f (place x (2 : Tensor K S))) / Real.log 2 ≤ ∑ i, dist f (x i) (x c) := by
  let A := Raw.shared K (Finset.univ : Finset S) 2
  have e : ofRaw A = 2 := shared_all K 2
  have h : ofRaw A ≠ 0 := by
    have hn := natCast_le (K := K) (S := S) (by decide : 1 ≤ 2)
    rw [Nat.cast_one, Nat.cast_ofNat, ← e] at hn
    exact fun hz => one_ne_zero (le_antisymm (hn.trans_eq hz) (zero_le _))
  let y := fun _ : S => x c
  have hy : place y (ofRaw A) = 1 := by
    change place y (shared K _ _) = _
    rw [place_shared, Finset.image_const Finset.univ_nonempty (x c)]
    simpa [wire] using wire_self K (x c) (n := 2) (by decide)
  have hd := (le_abs_self _).trans (price_transport f hf A h x y)
  rw [hy, e, map_one, Real.log_one, sub_zero] at hd
  have hc (s : S) : Fintype.card (A.leg s) = 2 := Fintype.card_fin 2
  rw [div_le_iff₀ (Real.log_pos (by norm_num)), Finset.sum_mul]
  simpa only [hc, Nat.cast_ofNat, y] using hd

variable [Nontrivial S]

/-- The scale on the marked sites is bounded by the total cost of moving
each leg of their binary diagonal to one common site. -/
theorem ordinary_restrict {D E : ℝ} {P : Tensor K T → ℝ}
    (hP : P ∈ ordinary K T D) (x : S → T)
    (he : ∀ i j, P (wire K (x i) (x j) 2) ≤ E) :
    (P ∘ place x) ∈ ordinary K S (E * Fintype.card S) := by
  obtain ⟨d, ⟨hd, _⟩, f, hf, rfl⟩ := hP
  let g : Tensor K S →* ℝ :=
    { toFun := fun A => f (place x A)
      map_one' := by rw [place_one, f.map_one]
      map_mul' := fun A B => by rw [place_mul, f.map_mul] }
  have hm : Monotone g := hf.comp (place_mono x)
  have hz : g 0 = 0 := by change f (place x 0) = _; rw [place_zero, f.map_zero]
  have ha (a b) : g (a + b) ≤ g a + g b :=
    (hf (place_add_le x a b)).trans_eq (f.map_add _ _)
  have hu (n : ℕ) : g (n : Tensor K S) ≤ (n : ℝ) := by
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      rw [Nat.cast_succ, Nat.cast_succ]
      exact (ha _ _).trans (add_le_add ih g.map_one.le)
  obtain ⟨p, hp, _, hn⟩ := TensorSpectrum.exists_power_of_monotone_multiplicative
    (fun n => g (n : Tensor K S))
    (fun _ _ _ _ => by rw [Nat.cast_mul, g.map_mul])
    (fun _ _ _ h => hm (natCast_le h))
    (fun n h => ⟨by simpa using hm (natCast_le h), hu n⟩)
  have ep : Real.log (g 2) / Real.log 2 = p := by
    have e := hn 2 (by decide)
    simp only [Nat.cast_ofNat] at e
    rw [e, Real.log_rpow (by norm_num), mul_div_cancel_right₀ _ (Real.log_pos (by norm_num)).ne']
  let c := Classical.arbitrary S
  have hb : d * p ≤ E * Fintype.card S := calc
    _ ≤ d * ∑ i, dist f (x i) (x c) :=
      mul_le_mul_of_nonneg_left (ep ▸ diagonal_cost x c f hf) hd
    _ = ∑ i, d * dist f (x i) (x c) := Finset.mul_sum _ _ _
    _ ≤ ∑ _i : S, E := Finset.sum_le_sum fun i _ => he i c
    _ = _ := by simp [mul_comm]
  rcases hp.eq_or_lt with rfl | hp
  · have ez : values d f ∘ place x = 0 := by
      funext a
      change d * (Real.log (g a) / Real.log 2) = 0
      by_cases h : a = 0
      · simp [h, hz]
      obtain ⟨n, h'⟩ := exists_bound a
      have hl : 1 ≤ g a := by simpa using hm (one_le a h)
      have hh := hm (h'.trans (natCast_le (Nat.le_succ n)))
      rw [hn (n + 1) (by omega), Real.rpow_zero] at hh
      rw [le_antisymm hh hl, Real.log_one, zero_div, mul_zero]
    rw [ez]
    exact zero_ordinary (by simpa using hb)
  · have hn' (n : ℕ) : g n = (n : ℝ) ^ p := by
      cases n with
      | zero => simp [hz, Real.zero_rpow hp.ne']
      | succ n => exact hn _ (by omega)
    obtain ⟨j, hj, ej⟩ := normalize_hom add_le_add_right zero_le g hm hz ha hp hn'
    refine ⟨d * p, ⟨mul_nonneg hd hp.le, hb⟩, j, hj, ?_⟩
    funext a
    change d * (Real.log (g a) / Real.log 2) = d * p * (Real.log (j a) / Real.log 2)
    by_cases h : a = 0
    · simp [h, hz]
    have hg : 0 < g a := price_place_pos f hf x h
    rw [ej, Real.log_rpow hg, mul_assoc, ← mul_div_assoc p, ← mul_assoc p,
      mul_inv_cancel₀ hp.ne', one_mul]

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-! # Limits of spectral wire metrics -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral Filter Topology

def WireModels (K Y : Type) [Field K] [PseudoMetricSpace Y] : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B] [Nonempty B] (z : B → Y) (D : ℝ),
    0 < D → (∀ i j, dist (z i) (z j) ≤ D) →
    ∃ P : Tensor K B → ℝ, (P = 0 ∨ P ∈ Tensor.ordinary K B (D * Fintype.card B)) ∧
      ∀ i j, P (Tensor.wire K i j 2) = dist (z i) (z j)

namespace WireModels
variable {K X Y B : Type} [Field K] [PseudoMetricSpace X] [PseudoMetricSpace Y]

private theorem point [Fintype B] [DecidableEq B] [Nontrivial B] (h : WireModels K Y) (z : B → Y) :
    ∃ d : ℝ, 0 ≤ d ∧ ∃ f : Tensor K B →+* ℝ, Monotone f ∧
      ∀ i j, dist (z i) (z j) = d * Tensor.dist f i j := by
  obtain ⟨D, hD⟩ := (Set.finite_range (fun p : B × B => dist (z p.1) (z p.2))).bddAbove
  have hb (i j : B) : dist (z i) (z j) ≤ max D 1 := (hD ⟨(i, j), rfl⟩).trans (le_max_left _ _)
  obtain ⟨P, hP, he⟩ := h B z _ (zero_lt_one.trans_le (le_max_right _ _)) hb
  have hp : P ∈ Tensor.ordinary K B (max D 1 * Fintype.card B) := by
    rcases hP with rfl | hp
    · exact Tensor.zero_ordinary (by positivity)
    · exact hp
  obtain ⟨d, hd, f, hf, rfl⟩ := hp
  exact ⟨d, hd.1, f, hf, fun i j => (he i j).symm⟩

theorem busemann (h : WireModels K Y) : Busemann Y := by
  intro t x y m a b n hx ha
  let z := ![x, y, m, a, b, n]
  obtain ⟨d, hd, f, hf, he⟩ := point h z
  change Divides t (z 0) (z 1) (z 2) at hx
  change Divides t (z 3) (z 4) (z 5) at ha
  change dist (z 2) (z 5) ≤ (1 - t.val) * dist (z 0) (z 3) + t.val * dist (z 1) (z 4)
  simp only [Divides, he] at hx ha ⊢
  rcases hd.eq_or_lt with rfl | hd
  · simp
  have cancel {u v w : ℝ} (h : d * u = w * (d * v)) : u = w * v :=
    mul_left_cancel₀ hd.ne' (h.trans (mul_left_comm _ _ _))
  have H := Tensor.busemann f hf (cancel hx.1) (cancel hx.2) (cancel ha.1) (cancel ha.2)
  linarith only [mul_le_mul_of_nonneg_left H hd.le]

theorem cuts (h : WireModels K Y) (hc : Sphere.ShiftedCrossing K) : CutBound (dist : Y → Y → ℝ) := by
  intro x x' y y' z z' w w' t u α β ht hu ha hb hq
  let e := ![x, x', y, y', z, z', w, w']
  obtain ⟨d, hd, f, hf, he⟩ := point h e
  have H := shifted_metric hc f hf 0 1 2 3 4 5 6 7 t u α β ht hu ha hb hq
  rcases H with h | h
  · left
    change t * (dist (e 0) (e 1) - dist (e 0) (e 4) - dist (e 1) (e 5)) +
      u * (dist (e 2) (e 3) - dist (e 2) (e 4) - dist (e 3) (e 5)) ≤ α * dist (e 4) (e 5)
    simp only [he]
    linarith only [mul_le_mul_of_nonneg_left h hd]
  · right
    change t * (dist (e 0) (e 1) - dist (e 0) (e 6) - dist (e 1) (e 7)) +
      u * (dist (e 2) (e 3) - dist (e 2) (e 7) - dist (e 3) (e 6)) ≤ β * dist (e 6) (e 7)
    simp only [he]
    linarith only [mul_le_mul_of_nonneg_left h hd]

/-- Finite models persist under pointwise limits of rescaled distances. -/
theorem limit (h : WireModels K X) (u : Ultrafilter ℕ) (x : ℕ → Y → X)
    (hh : ∀ a b, Tendsto (fun n : ℕ => ((n : ℝ) + 1) * dist (x n a) (x n b))
      (u : Filter ℕ) (𝓝 (dist a b))) : WireModels K Y := by
  intro B _ _ _ z D _ hz
  rcases subsingleton_or_nontrivial B with hB | hB
  · refine ⟨0, Or.inl rfl, fun i j => ?_⟩
    rw [Subsingleton.elim i j, dist_self]
    rfl
  choose d hd f hf he using fun n => point h (x n ∘ z)
  let P (n : ℕ) := Tensor.values (((n : ℝ) + 1) * d n) (f n)
  have hp (n : ℕ) : P n ∈ Tensor.ordinary K B (((n : ℝ) + 1) * d n) :=
    ⟨_, ⟨mul_nonneg (by positivity) (hd n), le_rfl⟩, f n, hf n, rfl⟩
  have hw (i j : B) : Tendsto (fun n => P n (Tensor.wire K i j 2))
      (u : Filter ℕ) (𝓝 (dist (z i) (z j))) := by
    refine (hh _ _).congr' (Eventually.of_forall fun n => ?_)
    change ((n : ℝ) + 1) * dist ((x n ∘ z) i) ((x n ∘ z) j) =
      ((n : ℝ) + 1) * d n * Tensor.dist (f n) i j
    rw [he, mul_assoc]
  have hb : ∀ᶠ n in (u : Filter ℕ), P n ∈ Tensor.ordinary K B ((D + 1) * Fintype.card B) := by
    have hd : ∀ᶠ n in (u : Filter ℕ), ∀ i j, P n (Tensor.wire K i j 2) ≤ D + 1 :=
      eventually_all.mpr fun i => eventually_all.mpr fun j =>
        (hw i j).eventually (eventually_le_nhds ((hz i j).trans_lt (lt_add_one D)))
    filter_upwards [hd] with n hn
    simpa only [Function.comp_def, Tensor.place_id] using Tensor.ordinary_restrict (hp n) id hn
  obtain ⟨Q, hQ, hq⟩ := (Tensor.compact_ordinary _).ultrafilter_le_nhds'
    (u.map P) (Filter.mem_map.mpr hb)
  have eq (i j : B) : Q (Tensor.wire K i j 2) = dist (z i) (z j) :=
    tendsto_nhds_unique (tendsto_pi_nhds.mp hq _) (hw i j)
  refine ⟨Q, Or.inr ?_, eq⟩
  have h' := Tensor.ordinary_restrict hQ id fun i j => (eq i j).le.trans (hz i j)
  simpa only [Function.comp_def, Tensor.place_id] using h'

end WireModels
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Compatible prices from finite wire models

For fixed marks, the possible compatible prices on them form a
directed family of compact sets as further names are prescribed.
Extension of scalars therefore only needs to preserve wire models.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
open scoped NNReal

variable {K L S : Type} [Field K] [Field L] [Fintype S] [DecidableEq S]

theorem map_wire (φ : K →+* L) (x y : S) (n : ℕ) :
    map φ (wire K x y n) = wire L x y n := by
  apply ofRaw_eq
  refine Raw.relabel (Equiv.refl _) (fun _ => Equiv.refl _) fun i s j => ?_
  change Fin n at i j
  change φ (if j = Raw.port {x, y} s i then 1 else 0) = if j = Raw.port {x, y} s i then 1 else 0
  split <;> simp

omit [DecidableEq S] in
theorem extend_field_real [Nonempty S] [Algebra K L] (f : Tensor K S →+* ℝ) (hf : Monotone f) :
    ∃ g : Tensor L S →+* ℝ, Monotone g ∧ ∀ A, g (map (algebraMap K L) A) = f A := by
  have h (A : Tensor K S) : 0 ≤ f A := by simpa using hf (zero_le A)
  let g : Tensor K S →+* ℝ≥0 :=
    { toFun := fun A => ⟨f A, h A⟩
      map_zero' := Subtype.ext (map_zero f)
      map_one' := Subtype.ext (map_one f)
      map_add' := fun a b => Subtype.ext (f.map_add a b)
      map_mul' := fun a b => Subtype.ext (f.map_mul a b) }
  obtain ⟨p, hp, he⟩ := extend_field L g hf
  exact ⟨NNReal.toRealHom.comp p, hp, fun A => congrArg NNReal.toReal (he A)⟩

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral Set

variable {K S Y : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]

theorem WireModels.extend_field [PseudoMetricSpace Y] (h : WireModels K Y)
    (L : Type) [Field L] [Algebra K L] : WireModels L Y := by
  intro B _ _ _ z D hp hb
  obtain ⟨P, h | ⟨d, hd, f, hf, rfl⟩, he⟩ := h B z D hp hb
  · rw [h] at he
    exact ⟨0, Or.inl rfl, he⟩
  · obtain ⟨g, hg, eg⟩ := Tensor.extend_field_real (L := L) f hf
    refine ⟨Tensor.values d g, .inr ⟨d, hd, g, hg, rfl⟩, fun i j => ?_⟩
    rw [← he i j, Tensor.values, Tensor.values, ← eg, Tensor.map_wire]

variable [MetricSpace Y]

theorem SpectralSpace.wireModels (h : SpectralSpace K Y) : WireModels K Y := by
  intro B _ _ _ x D hd hb
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact ⟨0, .inl rfl, fun i j => by rw [Subsingleton.elim i j, dist_self]; rfl⟩
  obtain ⟨P, _, hp⟩ := h B x
  have hz (i j : B) := (hb i j).trans (show D ≤ 2 * D by linarith)
  obtain ⟨Q, hQ, _, eq⟩ := (hp D hd hb).2 B x (fun i j => by cases i <;> cases j <;> exact hz _ _)
  have he (i j : B) : Q (Tensor.wire K (.inl i) (.inl j) 2) = dist (x i) (x j) := eq _ _
  exact ⟨Q ∘ Tensor.place Sum.inl,
    .inr (Tensor.ordinary_restrict hQ Sum.inl fun i j => (he i j).le.trans (hb i j)),
    fun i j => by rw [Function.comp_apply, Tensor.place_wire, he]⟩

private structure More (Y : Type) where
  U : Type
  [finiteSites : Fintype U]
  [eqSites : DecidableEq U]
  [inh : Nonempty U]
  z : U → Y

attribute [instance] More.finiteSites More.eqSites More.inh

private instance (s : More Y) : Nontrivial (S ⊕ s.U) :=
  ⟨.inl (Classical.arbitrary _), .inr (Classical.arbitrary _), by simp⟩

private def feasible (x : S → Y) (s : More Y) : Set (Tensor K S → ℝ) :=
  {P | ∃ D Q, Q ∈ Tensor.ordinary K (S ⊕ s.U) D ∧ (∀ A, Q (Tensor.pad s.U A) = P A) ∧
    ∀ i j, Q (Tensor.wire K i j 2) = dist (Sum.elim x s.z i) (Sum.elim x s.z j)}

private theorem feasible_bound (x : S → Y) (s : More Y) {P : Tensor K S → ℝ}
    (h : P ∈ feasible x s) (E : ℝ) (he : ∀ i j, dist (Sum.elim x s.z i) (Sum.elim x s.z j) ≤ E) :
    ∃ Q ∈ Tensor.ordinary K (S ⊕ s.U) (E * Fintype.card (S ⊕ s.U)),
      (∀ A, Q (Tensor.pad s.U A) = P A) ∧
      ∀ i j, Q (Tensor.wire K i j 2) = dist (Sum.elim x s.z i) (Sum.elim x s.z j) := by
  obtain ⟨_, Q, hQ, hp, hw⟩ := h
  refine ⟨Q, ?_, hp, hw⟩
  have h' := Tensor.ordinary_restrict hQ id fun i j => (hw i j).le.trans (he i j)
  simpa only [Function.comp_def, Tensor.place_id] using h'

omit [DecidableEq S] [Nonempty S] in
private theorem diameter_bound (z : S → Y) : ∃ D > 0, ∀ i j, dist (z i) (z j) ≤ D := by
  obtain ⟨D, hD⟩ := (Set.finite_range (fun p : S × S => dist (z p.1) (z p.2))).bddAbove
  exact ⟨max D 1, zero_lt_one.trans_le (le_max_right _ _),
    fun i j => (hD ⟨(i, j), rfl⟩).trans (le_max_left _ _)⟩

private theorem feasible_compact (x : S → Y) (s : More Y) : IsCompact (feasible (K := K) x s) := by
  let z := Sum.elim x s.z
  obtain ⟨D, _, hd⟩ := diameter_bound z
  let V := Tensor.ordinary K (S ⊕ s.U) (D * Fintype.card (S ⊕ s.U)) ∩
    {Q | ∀ i j, Q (Tensor.wire K i j 2) = dist (z i) (z j)}
  have hc : IsCompact V := by
    apply (Tensor.compact_ordinary _).inter_right
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_apply _) continuous_const
  let p (Q : Tensor K (S ⊕ s.U) → ℝ) := Q ∘ Tensor.pad s.U
  have hp : feasible x s = p '' V := by
    ext P
    constructor
    · intro h
      obtain ⟨Q, hQ, he, hw⟩ := feasible_bound x s h D hd
      exact ⟨Q, ⟨hQ, hw⟩, funext he⟩
    · rintro ⟨Q, ⟨hQ, hw⟩, rfl⟩
      exact ⟨_, Q, hQ, fun _ => rfl, hw⟩
  rw [hp]
  exact hc.image (continuous_pi fun _ => continuous_apply _)

private theorem feasible_mono (x : S → Y) (s t : More Y) (e : s.U → t.U)
    (he : ∀ i, t.z (e i) = s.z i) : feasible (K := K) x t ⊆ feasible x s := by
  rintro P ⟨_, Q, hQ, hp, hw⟩
  let f := Sum.map (id : S → S) e
  have hf (i) : Sum.elim x t.z (f i) = Sum.elim x s.z i := by
    cases i with
    | inl => rfl
    | inr => exact he _
  have H (i j) : Q (Tensor.wire K (f i) (f j) 2) = dist (Sum.elim x s.z i) (Sum.elim x s.z j) := by
    rw [hw, hf, hf]
  obtain ⟨D, _, hd⟩ := diameter_bound (Sum.elim x s.z)
  refine ⟨_, Q ∘ Tensor.place f, Tensor.ordinary_restrict hQ f (fun i j => (H i j).le.trans (hd i j)),
    fun A => ?_, fun i j => by rw [Function.comp_apply, Tensor.place_wire, H]⟩
  rw [Function.comp_apply, ← Tensor.place_inl, ← Tensor.place_comp,
    show f ∘ Sum.inl = Sum.inl from rfl, Tensor.place_inl, hp]

theorem WireModels.spectralSpace (h : WireModels K Y) : SpectralSpace K Y := by
  intro S _ _ _ x
  let V := feasible (K := K) x
  let _ : Nonempty (More Y) := ⟨⟨S, x⟩⟩
  have hc (s) := feasible_compact (K := K) x s
  have hn (s) : (V s).Nonempty := by
    obtain ⟨D, hd, hb⟩ := diameter_bound (Sum.elim x s.z)
    obtain ⟨Q, hQ, he⟩ := h _ _ D hd hb
    have ho : Q ∈ Tensor.ordinary K (S ⊕ s.U) (D * Fintype.card (S ⊕ s.U)) :=
      hQ.elim (fun e => e.symm ▸ Tensor.zero_ordinary (by positivity)) id
    exact ⟨Q ∘ Tensor.pad s.U, _, Q, ho, fun _ => rfl, he⟩
  have hd : Directed (· ⊇ ·) V := by
    intro s t
    let u : More Y := ⟨s.U ⊕ t.U, Sum.elim s.z t.z⟩
    exact ⟨u, feasible_mono x s u Sum.inl fun _ => rfl, feasible_mono x t u Sum.inr fun _ => rfl⟩
  obtain ⟨P, hP⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    V hd hn hc (fun s => (hc s).isClosed)
  have hp (s) := Set.mem_iInter.mp hP s
  refine ⟨P, ?_, fun D _ hD => ⟨hD, ?_⟩⟩
  · obtain ⟨_, Q, _, e, w⟩ := hp ⟨S, x⟩
    intro a b
    rw [← e, ← Tensor.place_inl, Tensor.place_wire]
    exact w _ _
  · intro U _ _ _ z hz
    exact feasible_bound x ⟨U, z⟩ (hp _) _ hz

theorem SpectralSpace.extend_field (h : SpectralSpace K Y) (L : Type) [Field L] [Algebra K L] :
    SpectralSpace L Y :=
  (h.wireModels.extend_field L).spectralSpace

end OAI.LinearAlgebra.MatrixExponent.Routing
end
