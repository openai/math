import OAI.LinearAlgebra.SpectralBooks.WireTile
import OAI.LinearAlgebra.SpectralBooks.ChordGraph.BoundedPatchReplacementClass

namespace OAI
/-! # From finite wire prices to identities in the port coordinates

The width of each unoriented edge is an integer. For rational widths these
are the numerators after multiplication by a common denominator.
-/

open scoped BigOperators NNReal Classical

namespace LinearAlgebra.SpectralBooks.ChordGraph

open SiteTensor

variable {k : ℕ} [Nonempty (Fin k)] (K : Type*) [Field K]

omit [Nonempty (Fin k)] in
private theorem binaryWire_ne_zero (e : Chord k) : wire K e ≠ 0 := by
  rw [wire, ne_eq, ofRaw_eq_zero_iff]
  apply ((Raw.diagonal (Fin 2) K (Fin 2)).group_ne_zero_iff _).mpr
  intro h
  have hh := congrFun h (fun _ => (0 : Fin 2))
  change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0 : K) at hh
  simp [Raw.diagonal, funext_iff] at hh

private theorem graphClass_eq_prod (w : Widths k) :
    graphClass K w = ∏ e, wire K e ^ w e :=
  Finsupp.prod_fintype w _ fun _ => pow_zero _

/-- Every independent wire assignment admits the all-zero label at each edge. -/
theorem graphClass_ne_zero (w : Widths k) : graphClass K w ≠ 0 := by
  rw [graphClass_eq_prod]
  exact Finset.prod_ne_zero_iff.mpr fun e _ => pow_ne_zero _ (binaryWire_ne_zero K e)

/-- A finite width assignment has log price equal to its weighted sum of
binary wire distances at the same normalized spectral point. -/
theorem logb_graphClass (w : Widths k)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin k) K → _ → Prop)) :
    Real.logb 2 (φ.val (graphClass K w) : ℝ) =
      ∑ e : Chord k, w e * rawWireDistance φ 1 e.1.1 e.1.2 := by
  let f := normalizedSpectrum.toRingHom φ
  change Real.logb 2 (f (graphClass K w) : ℝ) = _
  rw [graphClass_eq_prod, map_prod, NNReal.coe_prod]
  simp_rw [map_pow, NNReal.coe_pow]
  rw [Real.logb_prod]
  · simp only [Real.logb_pow, rawWireDistance, rawLogPrice, one_mul, wire, f]; rfl
  · intro e _
    apply pow_ne_zero
    exact (NNReal.coe_pos.mpr (spectral_value_pos φ (binaryWire_ne_zero K e))).ne'

/-- Collecting widths edge by edge realizes the tensor product of the individual wirings. -/
theorem graphClass_sum {J : Type*} [Fintype J] (g : J → Widths k) :
    graphClass K (∑ j, g j) = ∏ j, graphClass K (g j) := by
  have aux (S : Finset J) : graphClass K (∑ j ∈ S, g j) = ∏ j ∈ S, graphClass K (g j) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih => simp only [Finset.sum_insert hj, Finset.prod_insert hj, graphClass_add, ih]
  exact aux Finset.univ

/-- For arbitrarily large integer scales, the demand is the ordinary sum of
restricted supply wirings in its own port coordinates. Each supply width
is a sum of input widths with nonnegative integer multiplicities totaling
the scale, and the selector needs at most `η * b` bits. -/
theorem exists_finite_wire_tile {J : Type*} [Fintype J] [Nonempty J]
    (a : Widths k) (U : J → Widths k)
    (cover : ∀ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin k) K → _ → Prop),
      ∃ j, (∑ e : Chord k, a e * rawWireDistance φ 1 e.1.1 e.1.2) ≤
        ∑ e : Chord k, U j e * rawWireDistance φ 1 e.1.1 e.1.2)
    {η : ℝ} (hη : 0 < η) (N : ℕ) :
    ∃ b s : ℕ, N < b ∧ (s : ℝ) ≤ η * b ∧
      let R := raw K (b • a)
      ∃ L : ℕ, L ≤ 2 ^ s ∧ ∃ z : Fin L → (∀ i, R.Leg i) → K,
        R.coeff = ∑ l, z l ∧ ∀ l, ∃ n : J → ℕ, ∑ j, n j = b ∧
          ({R with coeff := z l} : Raw (Fin k) K).Restricts
            (raw K (∑ j, n j • U j)) := by
  have pos (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin k) K → _ → Prop))
      (w : Widths k) : 0 < (φ.val (graphClass K w) : ℝ) :=
    NNReal.coe_pos.mpr (spectral_value_pos φ (graphClass_ne_zero K w))
  have hcover (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin k) K → _ → Prop)) :
      ∃ j, φ.val (graphClass K a) ≤ φ.val (graphClass K (U j)) := by
    obtain ⟨j, hj⟩ := cover φ
    rw [← logb_graphClass K a φ, ← logb_graphClass K (U j) φ] at hj
    exact ⟨j, NNReal.coe_le_coe.mp ((Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      (pos φ a) (pos φ (U j))).mp hj)⟩
  obtain ⟨b, s, hb, hs, h⟩ := exists_finite_packet (graphClass K a) (fun j => graphClass K (U j))
    (graphClass_ne_zero K a) (fun j => graphClass_ne_zero K (U j)) hcover hη N
  obtain ⟨L, hL, z, hz, hz'⟩ := h (raw K (b • a)) (by rw [ofRaw_raw, graphClass_nsmul])
  refine ⟨b, s, hb, hs, L, hL, z, hz, fun l => ?_⟩
  obtain ⟨n, hn, hrest⟩ := hz' l
  exact ⟨n, hn, ofRaw_le_iff.mp (by simpa only [ofRaw_raw, graphClass_sum, graphClass_nsmul]
    using hrest)⟩

end LinearAlgebra.SpectralBooks.ChordGraph

end OAI
