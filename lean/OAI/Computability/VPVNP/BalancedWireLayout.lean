import OAI.Computability.VPVNP.BalancedCircuit
import OAI.Computability.VPVNP.WireSpectrum

/-!
# Spectral cost of the balanced circuit cuts

Place the coefficient tensor of an arithmetic circuit at its terminal parties. Each
balanced cut can choose its own two centers. Local contraction of the explicit
factors at those centers realizes the corresponding term, giving the product of wire
values used in the upper bound (4.5).
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial WireTensor
open scoped NNReal

variable {k : Type*} [Field k] {I J B : Type} {P : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype B] [Fintype P]

/-- Terminals in `S` use the first center, and the rest use the second. -/
def cutSide (S : Finset I) (i : I) : Bool := decide (i ∉ S)

/-- Place each party `i` at `place i` and give each joint assignment the cut matrix entry
indexed by its restrictions to `S` and its complement. -/
noncomputable def CutFactors.placed {S : Finset I} (F : CutFactors S B J k) (place : I → P) :
    WireTensor.Tensor k P :=
  placedTensor place (fun _ ↦ J) fun a ↦ F.matrix (fun i ↦ a i.val) (fun i ↦ a i.val)

/-- The term on this cut is a local restriction of the terminal and bridge wires. -/
theorem CutFactors.wire_restricts {S : Finset I} (F : CutFactors S B J k)
    (place : I → P) (center : Bool → P) :
    Restricts (wireNetwork (cutSource place center) (cutTarget (cutSide S) center)
      (cutBasis (fun _ ↦ J) B)) (F.placed place) := by
  let L (a : (i : I) → cutSide S i = false → J) (z : B) :=
    F.left (fun i ↦ a i.val (by simp [cutSide, i.property])) z
  let M (a : (i : I) → cutSide S i = true → J) (z : B) :=
    F.right z (fun i ↦ a i.val (by simpa only [cutSide, decide_eq_true_eq] using
      (Finset.mem_compl.mp i.property)))
  exact cutFactorization_restricts place (cutSide S) center (fun _ ↦ J) B L M

theorem CutFactors.spectralValue_le {S : Finset I} (A : CutFactors S B J k)
    (F : WireTensor.SpectralPoint k P) (place : I → P) (center : Bool → P) :
    F.value (A.placed place) ≤ F.value (wire (center false) (center true) B) *
      ∏ i, F.value (wire (place i) (center (cutSide S i)) J) := by
  have h := F.monotone (A.wire_restricts place center)
  rw [F.value_wireNetwork, Fintype.prod_option] at h
  exact h

/-- Spectral value of the full coefficient tensor, bounded by the wire networks of
the balanced terms only, each with independently chosen centers. -/
theorem Circuit.spectralValue_le_balanced_wires {s : ℕ} (c : Circuit k (I × J) s)
    (hI : 3 ≤ Fintype.card I) (F : WireTensor.SpectralPoint k P) (place : I → P)
    (centers : Finset I → Bool → P) :
    F.value (placedTensor place (fun _ ↦ J)
      (fun a ↦ c.polynomial.coeff (partyExponent Finset.univ a))) ≤
      ∑ S : Finset I with Fintype.card I ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * Fintype.card I,
        F.value (wire (centers S false) (centers S true) (Circuit.BalancedStates I J s)) *
          ∏ i, F.value (wire (place i) (centers S (cutSide S i)) J) := by
  classical
  obtain ⟨A, hcoeff, hbal⟩ := c.exists_balanced_cutFactors hI
  let cuts := Finset.univ.filter
    (fun S : Finset I ↦ Fintype.card I ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * Fintype.card I)
  let target := placedTensor place (fun _ ↦ J)
    (fun a ↦ c.polynomial.coeff (partyExponent Finset.univ a))
  have hsum : target.coeff = ∑ S ∈ cuts, ((A S).placed place).coeff := by
    funext u
    let a (i : I) := u (place i) i rfl
    change c.polynomial.coeff (partyExponent Finset.univ a) = _
    refine (hcoeff a).trans (Eq.trans ?_ (Finset.sum_apply u cuts
      (fun S ↦ ((A S).placed place).coeff)).symm)
    dsimp only [cuts]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    by_cases hS : Fintype.card I ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * Fintype.card I
    · simp only [hS]
      rfl
    · simp [hS, hbal S hS]
  have hs := F.value_sum_le (b := target.finiteBasis) cuts (fun S ↦ ((A S).placed place).coeff)
  change F.value target ≤ _
  rw [show target = WireTensor.Tensor.mk target.Basis target.finiteBasis
    (∑ S ∈ cuts, ((A S).placed place).coeff) from congrArg _ hsum]
  calc
    _ ≤ ∑ S ∈ cuts, F.value ((A S).placed place) := hs
    _ ≤ _ := Finset.sum_le_sum fun S _ ↦ (A S).spectralValue_le F place (centers S)

/-- Express the finite spectral estimate using the power law for each wire. Here
`r` is any numerical upper bound on the bridge dimension, and `q` is the terminal
dimension. The outer wire lengths add in the exponent of `q`. -/
theorem Circuit.spectralValue_le_balanced_cost {s r : ℕ} (c : Circuit k (I × J) s)
    (hI : 3 ≤ Fintype.card I) (hJ : 0 < Fintype.card J) (hr : 0 < r)
    (hwidth : Fintype.card (Circuit.BalancedStates I J s) ≤ r)
    (F : WireTensor.SpectralPoint k P) (place : I → P) (centers : Finset I → Bool → P) :
    (F.value (placedTensor place (fun _ ↦ J)
      (fun a ↦ c.polynomial.coeff (partyExponent Finset.univ a))) : ℝ) ≤
      ∑ S : Finset I with Fintype.card I ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * Fintype.card I,
        (r : ℝ) ^ F.wireDistance (centers S false) (centers S true) *
          (Fintype.card J : ℝ) ^ (∑ i, F.wireDistance (place i) (centers S (cutSide S i))) := by
  classical
  have hb := NNReal.coe_le_coe.mpr (c.spectralValue_le_balanced_wires hI F place centers)
  rw [NNReal.coe_sum] at hb
  refine hb.trans (Finset.sum_le_sum fun S _ ↦ ?_)
  rw [NNReal.coe_mul, NNReal.coe_prod, Real.rpow_sum_of_pos (by exact_mod_cast hJ)]
  apply mul_le_mul
  · rw [F.value_wire_equiv _ _ (Fintype.equivFin _), ← F.value_wire_eq_rpow _ _ hr]
    exact F.wireDimension_monotone _ _ hwidth
  · apply le_of_eq
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [F.value_wire_equiv _ _ (Fintype.equivFin J), F.value_wire_eq_rpow _ _ hJ]
  · exact Finset.prod_nonneg fun _ _ ↦ NNReal.coe_nonneg _
  · positivity

end VPVNP
end Computability
end OAI
