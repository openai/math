import OAI.Computability.VPVNP.ProjectedPowerObstruction
import OAI.Computability.VPVNP.TensorPowerCNFBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The tensor-power layout bound for the universal family

The finite-state tensor-power verifier uses source length at most a constant times
`((2^b)^12)^h`. Thus the comparison with an `n^C` circuit uses the exponent `12*C`.
The constant may depend on the number of parties and the fixed digit width, while the
exponent twelve is independent of both. The terminal tensor below uses cardinality
indices `Fin (2^b)`, as in the star-witness construction.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial WireTensor TensorPowerCNF

variable {k : Type*} [Field k] {I : Type} [Fintype I] [DecidableEq I]
    {P : Type*} [Fintype P] [Nonempty P]

/-- A layout whose scaled length lies below the normalized logarithm of the witness
has strictly smaller spectral growth. -/
theorem power_lt_of_scaled_logb {scale threshold cost v : ℝ} {b : ℕ} (hs : 0 < scale)
    (hb : 0 < b) (hv : 0 < v) (hcost : cost ≤ scale * threshold)
    (hval : threshold < Real.logb 2 v / (scale * b)) :
    (((2 ^ b : ℕ) : ℝ) ^ cost) < v := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ))]
  apply (Real.lt_logb_iff_rpow_lt (by norm_num : 1 < (2 : ℝ)) hv).mp
  calc
    (b : ℝ) * cost ≤ b * (scale * threshold) := mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg _)
    _ = threshold * (scale * b) := by ring
    _ < _ := (lt_div_iff₀ (mul_pos hs (Nat.cast_pos.mpr hb))).mp hval

omit [DecidableEq I] [Nonempty P] in
/-- A local reindexing of all terminal legs leaves their placed tensor's value unchanged. -/
theorem value_reindex_terminal_array {J L : Type} [Fintype J] [Fintype L] (F : SpectralPoint k P)
    (place : I → P) (e : J ≃ L) (A : (I → L) → k) :
    F.value (placedTensor place (fun _ ↦ J) (fun x ↦ A (e ∘ x))) =
      F.value (placedTensor place (fun _ ↦ L) A) := by
  let eqv (j : P) : ((r : I) → j = place r → J) ≃ ((r : I) → j = place r → L) :=
    Equiv.piCongrRight fun _ ↦ Equiv.piCongrRight fun _ ↦ e
  exact (F.value_eq_of_mutual (restricts_of_reindex eqv (fun _ ↦ rfl))).symm

omit [DecidableEq I] in
/-- The `h`-fold tensor form from the machine construction records the ordered
product of the selected tensor entries. -/
theorem TensorPowerCNF.coeff_form {b h : ℕ} (A : (I → Digit b) → k) (a : I → Word b h) :
    (form A h).coeff (partyExponent Finset.univ a) = ∏ t : Fin h, A (fun i ↦ a i t) := by
  classical
  simpa only [form, map_prod] using coeff_partyForm (fun x : I → Word b h ↦ ∏ t : Fin h, A (fun i ↦ x i t)) a

/-- Reindex the star witness by binary digits and convert its normalized log
lower bound into a strict spectral growth comparison for every balanced cut. -/
theorem exists_digit_layout_witness (F : SpectralPoint k P)
    (place : I → P) (centers : Finset I → Bool → P) {b C : ℕ} (hb : 0 < b)
    (A : (I → Fin (2^b)) → k) (hnz : A ≠ 0) {scale threshold : ℝ} (hs : 0 < scale)
    (hlower : threshold <
      Real.logb 2 (F.value (placedTensor place (fun _ ↦ Fin (2^b)) A)) / (scale * b))
    (hcost : ∀ S : Finset I, Fintype.card I ≤ 3*S.card → 3*S.card ≤ 2*Fintype.card I →
      (C : ℝ) * F.wireDistance (centers S false) (centers S true) +
        ∑ i, F.wireDistance (place i) (centers S (cutSide S i)) ≤ scale * threshold) :
    ∃ A' : (I → Digit b) → k, 0 < (F.value (placedTensor place (fun _ ↦ Digit b) A') : ℝ) ∧
      ∀ S : Finset I, Fintype.card I ≤ 3*S.card → 3*S.card ≤ 2*Fintype.card I →
        (Fintype.card (Digit b) : ℝ) ^ ((C : ℝ) * F.wireDistance (centers S false) (centers S true) +
          ∑ i, F.wireDistance (place i) (centers S (cutSide S i))) <
          (F.value (placedTensor place (fun _ ↦ Digit b) A') : ℝ) := by
  classical
  let e : Digit b ≃ Fin (2 ^ b) := Fintype.equivFinOfCardEq (by simp [Digit])
  let A' : (I → Digit b) → k := fun a ↦ A (e ∘ a)
  let v := (F.value (placedTensor place (fun _ ↦ Fin (2^b)) A) : ℝ)
  have heq : F.value (placedTensor place (fun _ ↦ Digit b) A') =
      F.value (placedTensor place (fun _ ↦ Fin (2^b)) A) :=
    value_reindex_terminal_array F place e A
  have hv : 0 < v := by
    have hnz' : (placedTensor place (fun _ ↦ Fin (2^b)) A).coeff ≠ 0 := by
      intro hz
      exact hnz (funext fun a ↦ congrFun hz (fun _ r _ ↦ a r))
    exact_mod_cast zero_lt_one.trans_le (F.one_le_value _ hnz')
  have hcard : Fintype.card (Digit b) = 2 ^ b := by simp [Digit]
  refine ⟨A', heq.symm ▸ hv, fun S hlo hhi ↦ ?_⟩
  rw [heq, hcard]
  exact power_lt_of_scaled_logb hs hb hv (hcost S hlo hhi) hlower

/-- A star witness strictly above every balanced layout precludes infinitely many
small-circuit lengths. The exponent of the layout's central wire includes the length
overhead of the concrete literal projection. -/
theorem not_small_universal_of_tensorPower_layout (F : SpectralPoint k P)
    (place : I → P) (centers : Finset I → Bool → P) {b C : ℕ} (hb : 0 < b) (hC : 0 < C)
    (hI : 3 ≤ Fintype.card I) (A : (I → Fin (2^b)) → k) (hnz : A ≠ 0)
    {scale threshold : ℝ} (hs : 0 < scale)
    (hlower : threshold <
      Real.logb 2 (F.value (placedTensor place (fun _ ↦ Fin (2^b)) A)) / (scale * b))
    (hcost : ∀ S : Finset I, Fintype.card I ≤ 3*S.card → 3*S.card ≤ 2*Fintype.card I →
      ((12*C : ℕ) : ℝ) * F.wireDistance (centers S false) (centers S true) +
        ∑ i, F.wireDistance (place i) (centers S (cutSide S i)) ≤ scale * threshold) :
    ¬ ∀ N, ∃ n ≥ N, circuitSize (map (Int.castRingHom k) (VPVNP.P n)) ≤ n^C := by
  classical
  obtain ⟨A', hv, hgap⟩ := exists_digit_layout_witness F place centers hb A hnz hs hlower hcost
  have hcard : Fintype.card (Digit b) = 2 ^ b := by simp [Digit]
  apply not_small_universal_of_power_projections F place centers A' (form A')
    (lengthCoefficient b (Fintype.card I)) 12 C (lengthCoefficient_pos _ _) (by decide) hC hI
    (hcard ▸ one_lt_pow₀ (by decide : 1 < (2 : ℕ)) hb.ne')
  · exact fun h a ↦ TensorPowerCNF.coeff_form A' a
  · intro h n hn
    exact projection A' hb h n (by simpa only [hcard] using hn)
  · exact hv
  · exact hgap

end VPVNP
end Computability
end OAI
