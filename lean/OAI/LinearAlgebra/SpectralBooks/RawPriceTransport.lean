import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping
import OAI.LinearAlgebra.SpectralBooks.WireTransport
import OAI.LinearAlgebra.SpectralBooks.WireSymmetry
import OAI.LinearAlgebra.SpectralBooks.SiteTransportChain

/-! # Transport and collapse for an actual spectral point

A move of one index uses one wire of the appropriate dimension. Adding such
moves gives the transport inequality for any two placements in the finite
site set. Moving indices across wires of price zero preserves the price.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

noncomputable section
open scoped NNReal

variable {I J : Type} {K : Type*} [Fintype I] [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)

/-- Binary wire distance in the placement supplied by a scaled spectral point. -/
def rawWireDistance (s t : J) : ℝ :=
  rawLogPrice φ c ((Raw.diagonal (Fin 2) K (Fin 2)).group ![s, t])

theorem rawWireDistance_symm (s t : J) : rawWireDistance φ c s t = rawWireDistance φ c t s := by
  unfold rawWireDistance rawLogPrice
  rw [ofRaw_eq_iff.mpr (Raw.grouped_wire_symm K (Fin 2) s t)]

private theorem diagonal_pair_ne_zero (D : Type) [Fintype D] [Nonempty D] :
    (Raw.diagonal (Fin 2) K D).coeff ≠ 0 := by
  classical
  let d := Classical.arbitrary D
  intro hzero
  have h := congrFun hzero (fun _ => d)
  have he (a : D) : (fun _ : Fin 2 => d) = (fun _ => a) ↔ d = a :=
    ⟨fun h => congrFun h 0, by rintro rfl; rfl⟩
  change (Raw.diagonal (Fin 2) K D).coeff (fun _ => d) = (0 : K) at h
  simp [Raw.diagonal, he] at h

omit [Nonempty J] in
/-- At a single occupied site the tensor is an ordinary vector, supplied by a
local map from the one-dimensional unit. -/
theorem Raw.group_const_restricts_one (T : Raw.{0} I K) (s : J) :
    (T.group (fun _ => s)).Restricts (Raw.one J K) := by
  classical
  let M (j : J) (b : (T.group (fun _ => s)).Leg j) (_ : (Raw.one J K).Leg j) : K :=
    if h : s = j then T.coeff (fun i => b ⟨i, h⟩) else 1
  refine ⟨M, fun x => ?_⟩
  let (j : J) : Unique ((Raw.one J K).Leg j) := inferInstanceAs (Unique PUnit)
  rw [Fintype.sum_unique]
  change T.coeff (fun i => x s ⟨i, rfl⟩) = 1 * ∏ j, M j (x j) PUnit.unit
  rw [one_mul, Finset.prod_eq_single s]
  · simp [M]
  · intro j _ hj
    simp [M, Ne.symm hj]
  · simp

/-- A placement with all indices at one point has price zero. -/
theorem rawLogPrice_const (hc : 0 ≤ c) (T : Raw.{0} I K) (s : J) :
    rawLogPrice φ c (T.group (fun _ => s)) = 0 := by
  apply le_antisymm _ (rawLogPrice_nonneg φ hc _)
  have h := rawLogPrice_mono φ hc (T.group_const_restricts_one s)
  simpa [rawLogPrice, φ.property.2.1] using h

@[simp] theorem rawWireDistance_self (hc : 0 ≤ c) (s : J) : rawWireDistance φ c s s = 0 := by
  have h : (![s, s] : Fin 2 → J) = fun _ => s := by funext i; fin_cases i <;> rfl
  simpa only [rawWireDistance, h] using rawLogPrice_const φ c hc (Raw.diagonal (Fin 2) K (Fin 2)) s

/-- The price increase under one move is bounded by the binary wire distance
times the base-two logarithm of the transported local dimension. -/
theorem rawLogPrice_move_le (hc : 0 ≤ c) (T : Raw.{0} I K) (hT : T.coeff ≠ 0)
    (a b : I → J) (i : I) (hagree : ∀ j, j ≠ i → a j = b j) :
    rawLogPrice φ c (T.group b) ≤ rawLogPrice φ c (T.group a) +
      rawWireDistance φ c (a i) (b i) * Real.logb 2 (Fintype.card (T.Leg i)) := by
  classical
  obtain ⟨x, _⟩ : ∃ x, T.coeff x ≠ 0 := by
    by_contra! h
    exact hT (funext h)
  let : Nonempty (T.Leg i) := ⟨x i⟩
  let f := ![a i, b i]
  have hd := ((Raw.diagonal (Fin 2) K (T.Leg i)).group_ne_zero_iff f).mpr
    (diagonal_pair_ne_zero (K := K) (T.Leg i))
  have h := rawLogPrice_mono φ hc (Raw.move_restricts_with_wire T a b i hagree)
  rw [rawLogPrice_mul φ c _ _ ((T.group_ne_zero_iff a).mpr hT) hd,
    rawLogPrice_group_diagonal] at h
  exact h

/-- Transporting one end of a binary wire through a third site gives the
triangle inequality for its price. -/
theorem rawWireDistance_triangle (hc : 0 ≤ c) (s t u : J) :
    rawWireDistance φ c s u ≤ rawWireDistance φ c s t + rawWireDistance φ c t u := by
  let W := Raw.diagonal (Fin 2) K (Fin 2)
  have h := rawLogPrice_move_le φ c hc W (diagonal_pair_ne_zero (Fin 2))
    ![s, t] ![s, u] 1 (by intro i hi; fin_cases i <;> simp_all)
  simpa [W, rawWireDistance, Raw.diagonal, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    using h

/-- The transport inequality from the preliminaries, derived from local linear maps. -/
theorem rawLogPrice_transport (hc : 0 ≤ c) (T : Raw.{0} I K) (x y : I → J) :
    |rawLogPrice φ c (T.group x) - rawLogPrice φ c (T.group y)| ≤
      ∑ i, rawWireDistance φ c (x i) (y i) * Real.logb 2 (Fintype.card (T.Leg i)) := by
  by_cases hT : T.coeff = 0
  · have h (a : I → J) : (T.group a).coeff = 0 := funext fun y => congrFun hT _
    rw [rawLogPrice_zero φ c _ (h x), rawLogPrice_zero φ c _ (h y), sub_self, abs_zero]
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (rawLogPrice_nonneg φ hc _)
    rcases (Fintype.card (T.Leg i)).eq_zero_or_pos with hi | hi
    · simp [hi]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hi)
  · exact abs_price_sub_le_transport _ _ _ (rawWireDistance_symm φ c)
      (rawLogPrice_move_le φ c hc T hT) x y

/-- Regrouping any number of indices over zero-distance pairs preserves their price. -/
theorem rawLogPrice_eq_of_collapsed (hc : 0 ≤ c) (T : Raw.{0} I K) (x y : I → J)
    (h : ∀ i, rawWireDistance φ c (x i) (y i) = 0) :
    rawLogPrice φ c (T.group x) = rawLogPrice φ c (T.group y) := by
  have ht := rawLogPrice_transport φ c hc T x y
  simpa [h, sub_eq_zero] using ht

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
