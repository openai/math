import OAI.Computability.VPVNP.ShiftedCrossing
import Lemmata.FockCircuits.Families

/-!
# The two-wire identity with integral coefficients

Section 4.1 of *An explicit VNP family requires superpolynomial border circuit size over every
field* uses a wire carrying a subset of the modes, together with a wire carrying an element of
`Fin q`. The paper's energy is half the integer `doubledEnergy`. The shared index is a pair
consisting of a mode and an actual occupation state, which can serve as the state wire for
the next application of the identity.

The homogeneous dual family and marked-mode identity come from Kirill Khoruzhii's Lemmata entry
[Crossing Decomposition for Subquadratic Noncommutative Circuits](https://github.com/ZIB-IOL/lemmata/blob/a2dd430f283febd755a6ee6932d0b0fdabfb330c/docs/crossing-decomposition/index.md),
licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
open Lemmata.FockCircuits.CrossingCircuit Lemmata.FockCircuits.Families
open VPVNP.Crossing (cutoffCount IntegralCrossing integralCrossing_of_factors)
open scoped BigOperators

/-- A subset of modes of energy at most `E`, in the manuscript's half-integral units. -/
abbrev EnergyState (E : ℕ) := ↥(fullCutoff E)

/-- Conversion between the cutoffs used by the two papers. -/
theorem energyState_card (E : ℕ) : Fintype.card (EnergyState E) = cutoffCount (2 * E) :=
  (Fintype.card_coe _).trans (card_fullCutoff_eq_sum E)

/-- The wire labels are represented by distinct states of the same positive energy. One
choice works for every incoming state energy bound `E`. -/
structure WireStates (H q : ℕ) where
  /-- Twice the common energy of the states, also the number of mode labels. -/
  weight : ℕ
  /-- Positivity excludes the vacuum slice. -/
  positive : 0 < weight
  /-- The number of modes is at most `2H`. -/
  weight_le : weight ≤ 2 * H
  /-- Distinct wire labels select distinct occupation states. -/
  states : Fin q ↪ EnergyState H
  /-- All chosen states belong to the indicated homogeneous slice. -/
  energy_eq : ∀ i, doubledEnergy (states i).val = weight

/-- Pigeonholing the nonvacuum states into positive half-integral energy levels yields the
choice of states used by the crossing. -/
theorem exists_wireStates (H q : ℕ) (hH : 0 < H) (hcap : 2 * H * q < cutoffCount (2 * H)) :
    Nonempty (WireStates H q) := by
  have hcount : stateCount H = cutoffCount (2 * H) := card_fullCutoff_eq_sum H
  obtain ⟨W, S, hW, hWH, hcard, hS⟩ := exists_homogeneous_family H q hH (by omega)
  let e := (Finset.equivFinOfCardEq hcard).symm
  let toState (s : ↥S) : EnergyState H :=
    ⟨s.val, mem_fullCutoff.mpr ((hS s.val s.property).le.trans hWH)⟩
  have inj : Function.Injective toState := fun _ _ h => Subtype.ext (congrArg (fun z : EnergyState H => z.val) h)
  exact ⟨⟨W, hW, hWH, e.toEmbedding.trans ⟨toState, inj⟩, fun i => hS _ (e i).property⟩⟩

namespace WireStates

variable {H q : ℕ} (w : WireStates H q) (E : ℕ)

/-- Regard the input labels as states in the common `E + H`-mode Fock space. -/
def labels : Fin q ↪ Index (E + H) :=
  w.states.trans (cutoffEmbedding (Nat.le_add_left H E))

private abbrev action : EnergyState E ↪ Index (E + H) := cutoffEmbedding (Nat.le_add_right E H)
private abbrev middle : EnergyState (E + H) ↪ Index (E + H) := cutoffEmbedding le_rfl

/-- Coefficients for the two cuts. Each entry is an integral fermionic mode matrix entry.
The reverse-cut sign is included in its left factor. -/
noncomputable def factors (reverse left : Bool) :
    Fin w.weight × EnergyState (E + H) → Fin q → EnergyState E → ℤ :=
  match reverse, left with
  | false, true => coefficientA ℤ (dualFamily ℤ (w.labels E)) (action E) (middle (E := E))
  | false, false => coefficientB ℤ (bareFamily ℤ (w.labels E)) (action E) (middle (E := E))
  | true, true => fun s i I => -sigma w.weight *
      coefficientC ℤ (dualFamily ℤ (w.labels E)) (action E) (middle (E := E)) s i I
  | true, false => coefficientD ℤ (bareFamily ℤ (w.labels E)) (action E) (middle (E := E))

/-- Lemma 4.1 on actual occupation states. Both matrix products in (A.2) have the same
intermediate cutoff. The second product reverses the assignments of the two endpoint states. -/
theorem coefficient_identity (i j : Fin q) (I J : EnergyState E) :
    (∑ k, w.factors E false true k i I * w.factors E false false k j J) +
      (∑ k, w.factors E true true k i J * w.factors E true false k j I) =
      (if i = j then 1 else 0) * (if I = J then 1 else 0) := by
  have h := family_coefficient_identity ℤ (w.labels E) (action E) (middle (E := E)) w.positive
    w.energy_eq (cutoffEmbedding_energy _) (cutoffEmbedding_covers _) (by have := w.weight_le; omega)
    i j I J
  simp only [Int.cast_id] at h
  simp only [factors, mul_assoc, ← Finset.mul_sum]
  rw [neg_mul, ← sub_eq_add_neg, h]
  split_ifs <;> simp

end WireStates

/-- Numbered-wire form of the integral crossing in Section 4.1, ready for iteration.
There are `2H` mode labels after padding and `Q(E+H)` intermediate states on each cut. -/
theorem integralCrossing (H E q : ℕ) (hH : 0 < H) (hcap : 2 * H * q < cutoffCount (2 * H)) :
    Nonempty (IntegralCrossing q (cutoffCount (2 * E))
      ((2 * H) * cutoffCount (2 * (E + H))) ((2 * H) * cutoffCount (2 * (E + H)))) := by
  obtain ⟨w⟩ := exists_wireStates H q hH hcap
  have hcard : Fintype.card (Fin w.weight × EnergyState (E + H)) ≤
      2 * H * cutoffCount (2 * (E + H)) := by
    rw [Fintype.card_prod, Fintype.card_fin, energyState_card]
    exact Nat.mul_le_mul_right _ w.weight_le
  exact integralCrossing_of_factors (Fintype.card_fin q) (energyState_card E) hcard hcard
    (w.factors E false true) (w.factors E false false)
    (w.factors E true true) (w.factors E true false) (w.coefficient_identity E)

end Crossing

end BorderVNP
end Computability
end OAI
