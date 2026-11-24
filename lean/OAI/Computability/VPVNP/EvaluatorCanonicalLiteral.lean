import OAI.Computability.VPVNP.EvaluatorLiteralResources
import OAI.Computability.VPVNP.LabelEvaluatorCanonical
import OAI.Computability.VPVNP.EvaluatorAdviceBounds

/-!
# The literal evaluator for the canonical finite slice

The basis and the unit ordinal used by the tape program are the dense
ordinals furnished by the monomial prefix-rank queries. The physical matrix
reader receives the source ordinal before the destination ordinal. The
algebraic query returns the coefficient in the opposite order.

The point-count bound gives an index word width fixed independently of the
choice of pin values, the prime and the binary exponents.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LabelEvaluator

open MvPolynomial FiniteSlice RAMTape Evaluator SliceArithmetic
open Evaluator.MatrixCallbacks EvaluatorProgramRawInput Evaluator.BinaryMachine
open RadicalCertificate.MonomialIndex

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩
/-- The finite enumeration of the slice ground field used to express canonical evaluator
coordinates and bound the number of point ordinals. -/
noncomputable local instance canonicalGroundFintype (p : Nat.Primes) (t d : ℕ) :
    Fintype (Ground p t d) := Fintype.ofFinite _
/-- Decidable equality on the finite slice ground field used by the canonical
coordinate-algebra construction. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : DecidableEq (Ground p t d) := Classical.decEq _
/-- The algebra structure on the ambient field induced by the chosen embedding of the finite
slice ground field. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra

variable {p : Nat.Primes} {t d m : ℕ} {ι : Type*} {F : ι → MvPolynomial (Fin t) ℤ}
variable (M : Model p d F) {read : Fin m → (Fin t → ℕ) → ℤ}
variable (D : (M.queryData read).Canonical (E := Ambient p) (sliceIdeal p d F M.pins M.values))

include D in
/-- The number of dense ordinals is bounded by the paper's geometric
point count for the chosen slice. -/
theorem Model.canonical_dimension_le : (M.queryData read).dimension ≤ pointCountBound t d := by
  let I := sliceIdeal p d F M.pins M.values
  let V := zeroLocus (Ambient p) I
  let : Fintype V := M.finite.fintype
  have hr := (coordinateAlgebra_finite_finrank (E := Ambient p) I).2
  have he : Module.finrank (Ground p t d) (CoordinateAlgebra (Ground p t d) V) = (M.queryData read).dimension := by
    simpa using Module.finrank_eq_card_basis D.denseBasis
  rw [he, ← Nat.card_eq_fintype_card] at hr
  exact hr.trans M.pointCount_le

/-- An extra bit lets the register store the dimension itself, including at a power of two. -/
def ordinalWidth (t d : ℕ) := Nat.clog 2 (pointCountBound t d) + 1

include D in
theorem Model.canonical_dimension_fits : (M.queryData read).dimension < 2^(ordinalWidth t d) := by
  have h := (M.canonical_dimension_le D).trans (Nat.le_pow_clog (by decide : 1 < 2) _)
  have hpos : 0 < 2^(Nat.clog 2 (pointCountBound t d)) := Nat.two_pow_pos _
  rw [ordinalWidth, pow_succ]
  omega

theorem ordinalWidth_polynomiallyBounded {t d : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n)) :
    PolynomiallyBounded (fun n => ordinalWidth (t n) (d n)) :=
  (pointCountBound_clog ht hd).add (.const 1)

variable {P : Type} [DecidableEq P] [Fintype P] {g v w Z : ℕ} {c : SliceArithmetic.Vector p.val (g+1)}

variable (hdim : (M.queryData read).dimension < 2^v)
/-- The dimension of the canonical coordinate-algebra presentation encoded in a v-bit word for
the evaluator. -/
noncomputable abbrev Model.dimensionWord : BurstRAM.Word v := ⟨(M.queryData read).dimension, hdim⟩
local notation "dimWord" => M.dimensionWord hdim
local notation "unitOrd" => D.ordinal.symm D.presentation.unitIndex
local notation "ground" => Ground p t d
local notation "ports" => MachinePort (WeightedStep.Port P)

/-- Instantiate equation (8.2) and the uniform head bound on the canonical
Macaulay presentation. Both assertions concern the same literal two-tape
program and the same raw input. -/
theorem Model.canonical_literal_evaluator
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p.val] ground)
    (hcoord : ∀ y, SliceEvaluator.primeCoordinate p.val ground (φ (value (modulus c) y)) =
      ((y (0 : Fin (g+1))).val : ZMod p.val))
    (ps : List (WeightedStep.Port P)) (hps : ps.Nodup) (hall : ∀ i, i ∈ ps)
    (frob label : FiniteRoutine (ReadPort P)) (extra : Stacks P) (extraSpace : ℕ)
    (hextra : ∀ i, (extra i).length ≤ extraSpace) (hw : Word.workingWidth p.val ≤ w)
    (divisor : List Bool) (hd : TapeWord.value divisor = Fintype.card ground)
    (FT LT peak : ℕ)
    (hf : ReadsEntryWithin φ dimWord extra frob w 0 FT peak
      (fun src dest => (M.queryData read).matrixEntry .frobenius dest src))
    (hl : ∀ j : Fin t, ReadsEntryWithin φ dimWord extra label w j.val LT peak
      (fun src dest => (M.queryData read).matrixEntry (.label j) dest src))
    (es : Fin t → BurstRAM.Word Z) (ticks : ℕ)
    (hclock : let raw := advice ps t divisor (payload φ dimWord extra w (unitOrd,1)) ++ runtime es
      let adv := adviceCap ps.length t divisor.length (WeightedStep.bankSpace v (g+1) w extraSpace)
      tapeTicks raw.length (Fintype.card ports) (fullTicks t Z divisor.length (TapeWord.value divisor)
        adv (WeightedStep.ticks v (g+1) w FT) (WeightedStep.ticks v (g+1) w LT) v w) ≤ ticks) :
    let E := MatrixCallbacks.program ps frob label
    let raw := advice ps t divisor (payload φ dimWord extra w (unitOrd,1)) ++ runtime es
    let adv := adviceCap ps.length t divisor.length (WeightedStep.bankSpace v (g+1) w extraSpace)
    (UniversalMachine.paths E ticks (UniversalMachine.initial E raw) : ZMod p.val) =
      (M.withCanonicalPresentation D).functional (∏ j, M.labels j ^ (es j).val) ∧
      ∀ bits, let dis := choiceDisplacement E (UniversalMachine.initial E raw) bits
        StackCompiler.HeadBox (headRadius (Fintype.card ports)
          (fullSpace t Z divisor.length (workspace v (g+1) w extraSpace peak) adv v w)) dis.1 dis.2 := by
  have hf' : ReadsEntryWithin φ dimWord extra frob w 0 FT peak
      ((LinearMap.toMatrixAlgEquiv D.denseBasis) (FiniteField.frobeniusAlgHom ground M.algebra).toLinearMap).transpose := by
    have h := D.frobenius_transition (show (M.queryData read).fieldOrder = Fintype.card ground from rfl)
    exact (show _ = _ from funext fun i => funext (h i)) ▸ hf
  have hl' (j : Fin t) : ReadsEntryWithin φ dimWord extra label w j.val LT peak
      ((LinearMap.toMatrixAlgEquiv D.denseBasis) (LinearMap.mulLeft ground (M.labels j))).transpose := by
    have h := D.label_transition j
    exact (show _ = _ from funext fun i => funext (h i)) ▸ hl j
  obtain ⟨h,space⟩ := literal_from_bounded_readers ps frob label φ dimWord extra extraSpace hextra
    unitOrd D.denseBasis M.labels es divisor hps hall hw hd FT LT peak hf' hl' D.denseBasis_unit D.unit_ordinal
    hcoord ticks hclock
  exact ⟨h.trans (D.functional_apply _).symm, space⟩

end LabelEvaluator

end VPVNP
end Computability
end OAI
