import OAI.LinearAlgebra.SpectralBooks.SelectorSubrank
import OAI.LinearAlgebra.SpectralBooks.StrassenRank
import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionPower

namespace OAI
/-! # Ordinary restrictions of weighted port graphs from strict spectral comparison -/

namespace ThreeFlat.RouteUnits

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators Classical NNReal
noncomputable section

variable {V E J : Type} [Fintype V] [Nonempty V] [Fintype E] [Fintype J]
variable (F : Type*) [Field F]

/-- Pinning unused labels decreases the width of each edge independently. -/
theorem portWiring_restricts_of_width_le (G : PortGraph V E) (w w' : E → ℕ)
    (fits : ∀ e, w e ≤ w' e) :
    (G.rawWiring F (fun e => Fin (2 ^ w e))).Restricts
      (G.rawWiring F (fun e => Fin (2 ^ w' e))) := by
  apply ofRaw_le_iff.mp
  rw [G.ofRaw_rawWiring, G.ofRaw_rawWiring]
  refine Finset.prod_le_prod fun e _ => ofRaw_le_iff.mpr ?_
  apply Raw.group_restricts
  exact Raw.diagonal_restricts_of_embedding _ _
    (Fin.castLEEmb (Nat.pow_le_pow_right (by decide) (fits e)))

private abbrev wiredClass (G : PortGraph V E) (w : E → ℕ) :=
  ofRaw (G.rawWiring F (fun e => Fin (2 ^ w e)))

private theorem wiredClass_eq (G : PortGraph V E) (w : E → ℕ) :
    wiredClass F G w = ∏ e, ofRaw (G.edgeRaw F (fun _ => Fin 2) e) ^ w e := by
  rw [wiredClass, PortGraph.ofRaw_rawWiring]
  simp only [PortGraph.edgeRaw, ofRaw_group_diagonal_fin_pow]

private theorem wiredClass_scaled (G : PortGraph V E) (w : E → ℕ) (n : ℕ) :
    wiredClass F G (fun e => n * w e) = (wiredClass F G w) ^ n := by
  rw [wiredClass_eq, wiredClass_eq, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro e _
  rw [Nat.mul_comm, pow_mul]

omit [Nonempty V] in
private theorem wiredClass_ne_zero (G : PortGraph V E) (w : E → ℕ) :
    wiredClass F G w ≠ 0 := by
  rw [ne_eq, ofRaw_eq_zero_iff]
  intro h
  have eq := congrFun h (fun _ _ => 0)
  change G.wiring (fun e => Fin (2 ^ w e)) (fun _ _ => 0) = (0 : F) at eq
  simp [PortGraph.wiring] at eq

private theorem log_wiredClass (G : PortGraph V E) (w : E → ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} V F → _ → Prop)) :
    Real.logb 2 (φ.val (wiredClass F G w) : ℝ) =
      ∑ e, (w e : ℝ) * rawWireDistance φ 1 (G.tail e) (G.head e) := by
  change Real.logb 2 ((normalizedSpectrum.toRingHom φ) (wiredClass F G w) : ℝ) = _
  rw [wiredClass_eq, map_prod, NNReal.coe_prod, Real.logb_prod]
  · apply Finset.sum_congr rfl
    intro e _
    simp only [map_pow, NNReal.coe_pow, Real.logb_pow, rawWireDistance, rawLogPrice, one_mul]
    rfl
  · intro e _
    rw [map_pow, NNReal.coe_pow]
    apply pow_ne_zero
    apply ne_of_gt
    apply NNReal.coe_pos.mpr
    apply spectral_value_pos φ
    rw [ne_eq, ofRaw_eq_zero_iff]
    apply ((Raw.diagonal (Fin 2) F (Fin 2)).group_ne_zero_iff _).2
    intro h
    have hh := congrFun h (fun _ => (0 : Fin 2))
    change (Raw.diagonal (Fin 2) F (Fin 2)).coeff _ = (0 : F) at hh
    rw [Raw.diagonal_coeff_at (0 : Fin 2)] at hh
    simp at hh

/-- A connected supply graph absorbs the common diagonal selector. Each supply edge
carries one extra bit per repetition and a fixed number of bits independent of the repetition count. -/
theorem exists_connected_port_restriction (D : PortGraph V E) (G : PortGraph V J)
    (w : E → ℕ) (d b : ℕ) (r : V)
    (conn : ∀ f : V → Bool, (∀ e, f (G.tail e) = f (G.head e)) → ∀ v, f v = f r)
    (cover : ∀ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} V F → _ → Prop),
      (d : ℝ) * (∑ e, (w e : ℝ) * rawWireDistance φ 1 (D.tail e) (D.head e)) ≤
        (b : ℝ) * ∑ e, rawWireDistance φ 1 (G.tail e) (G.head e)) :
    ∃ c : ℕ, ∀ t : ℕ, 0 < t →
      (D.rawWiring F (fun e => Fin (2 ^ ((d*t) * w e)))).Restricts
        (G.rawWiring F (fun _ => Fin (2 ^ ((b+1)*t+c)))) := by
  let X := wiredClass F D w
  let Y := wiredClass F G (fun _ => 1)
  have two : (2 : TensorClass.{0} V F) ≤ Y := G.two_le_rawWiring_of_connected F r conn
  have hx : X ≠ 0 := wiredClass_ne_zero F D w
  have hy : Y ≠ 0 := wiredClass_ne_zero F G _
  have strict (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} V F → _ → Prop)) :
      φ.val (X ^ d) < φ.val (Y ^ (b+1)) := by
    let v := normalizedSpectrum.toRingHom φ
    have hv : v 2 ≤ v Y := φ.2.2.2.2.2 _ _ two
    have hv' : (1 : ℝ) < (φ.val Y : ℝ) := by
      have ht : (2 : ℝ≥0) ≤ φ.val Y := (map_ofNat v 2).symm.le.trans hv
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℝ≥0) < 2) ht)
    have hp := Real.logb_pos (by norm_num : (1 : ℝ) < 2) hv'
    have heq : Real.logb 2 (φ.val Y : ℝ) = ∑ e, rawWireDistance φ 1 (G.tail e) (G.head e) := by
      simpa only [Nat.cast_one, one_mul, Y] using log_wiredClass F G (fun _ => 1) φ
    have heq' := log_wiredClass F D w φ
    have hc := cover φ
    rw [← heq, ← heq'] at hc
    apply NNReal.coe_lt_coe.mp
    apply (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2)
      (NNReal.coe_pos.mpr (spectral_value_pos φ (pow_ne_zero d hx)))
      (NNReal.coe_pos.mpr (spectral_value_pos φ (pow_ne_zero (b+1) hy)))).mp
    change Real.logb 2 (v (X ^ d) : ℝ) < Real.logb 2 (v (Y ^ (b+1)) : ℝ)
    simp only [map_pow, NNReal.coe_pow, Real.logb_pow, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact lt_add_of_le_of_pos hc hp
  obtain ⟨c, _, comp⟩ := strictSpectralComparison V F (X^d) (Y^(b+1))
    (pow_ne_zero _ hx) (pow_ne_zero _ hy) strict
  have hcast : (c : TensorClass.{0} V F) ≤ (2^c : ℕ) := by
    rw [← ofRaw_diagonal_fin_eq_natCast V F c, ← ofRaw_diagonal_fin_eq_natCast V F (2^c),
      ofRaw_le_iff]
    exact Raw.diagonal_restricts_of_embedding _ _ (Fin.castLEEmb (Nat.le_of_lt Nat.lt_two_pow_self))
  have cap : (c : TensorClass.{0} V F) ≤ Y ^ c := hcast.trans (by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using pow_le_pow_left' two c)
  refine ⟨c, fun t ht => ofRaw_le_iff.mp ?_⟩
  change wiredClass F D (fun e => (d*t) * w e) ≤ wiredClass F G (fun _ => (b+1)*t+c)
  rw [wiredClass_scaled]
  have hsup := wiredClass_scaled F G (fun _ => 1) ((b+1)*t+c)
  simp only [Nat.mul_one] at hsup
  rw [hsup]
  calc
    X^(d*t) ≤ c • Y^((b+1)*t) := by simpa [pow_mul] using comp t ht
    _ ≤ Y^c * Y^((b+1)*t) := by
      simpa only [nsmul_eq_mul] using SiteTensor.mul_mono cap (le_refl (Y^((b+1)*t)))
    _ = Y^((b+1)*t+c) := by rw [pow_add, mul_comm]

end
end ThreeFlat.RouteUnits

end OAI
