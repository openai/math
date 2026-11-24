import OAI.Computability.VPVNP.FixedProgramModelData

/-!
# The model's label order on the native evaluator input

The first half stores productions first and motif variables second. The model's
advice specifies their positions in the joint label order. The native ordinal
words and the reindexed runtime exponent field are exactly the words of the
fixed diagonal program, including the length-dependent width of each counter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression LiveProgram LiveEvaluatorEncoding JointLabelSystem
open scoped Fin.CommRing

variable {K : Type*} [Field K] {S : BlockSchedule K} (D : Program) (B : S.Templates)
variable {n C : ℕ}

/-- Number of dense exponent coordinates in the physical group at this input length. -/
abbrev physicalLabelCount := D.constants.labels.eval (D.geometry n)
/-- Number of bits allocated to each exponent counter in the physical group. -/
abbrev physicalCounterWidth := D.constants.Z.eval (D.geometry n)

theorem physicalLabelCount_eq (exponent : D.constants.circuitExponent = C)
    (motifs : D.constants.motifLabels = Fintype.card B.Entry) :
    physicalLabelCount D (n := n) = B.denseCount n C := by
  change D.constants.grammarLabels.eval (D.geometry n) + D.constants.motifLabels = _
  rw [D.constants.grammarLabels_eq, exponent, motifs]; rfl

theorem physicalCounterWidth_eq : physicalCounterWidth D (n := n) = D.counterWidth n := by
  simp only [physicalCounterWidth,Constants.Z,Constants.height,eval_mul,PublicExpr.eval_natPow]
  rfl

theorem physicalRadius_eq : D.constants.radius.eval (D.geometry n) = n^D.constants.radiusPower := by
  rw [Constants.radius, PublicExpr.eval_natPow]; rfl

variable (denseCount : physicalLabelCount D (n := n) = B.denseCount n C)

/-- The native scatter has a single index type, whereas the model names
both the dense and the formal label count. Their equality transports only
the bounds of the indices. The permutation itself is the model's one. -/
noncomputable def nativeLabelOrder : Fin (physicalLabelCount D (n := n)) ≃ Fin (physicalLabelCount D (n := n)) :=
  (finCongr denseCount).trans ((FixedRows.labelOrder B.Entry n C).trans
    (finCongr (denseCount.trans (FixedRows.labelOrder_length B.Entry n C))).symm)

/-- Encode the evaluator ordinal of each physical label as a binary word in the advice
permutation. -/
noncomputable def nativeOrdinalWords (i : Fin (physicalLabelCount D (n := n))) :
    Word (Nat.clog 2 (physicalLabelCount D (n := n))) :=
  ⟨(nativeLabelOrder D B denseCount i).val,
    (nativeLabelOrder D B denseCount i).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩

theorem nativeOrdinal_value (i : Fin (physicalLabelCount D (n := n))) :
    (nativeOrdinalWords D B denseCount i).val = (orderWord B n C (i.cast denseCount)).val := rfl

private theorem tape_congr {a b za zb : ℕ} (ht : a=b) (hz : za=zb)
    (x : Fin a → Word za) (y : Fin b → Word zb) (he : ∀ j, (x j).val = (y (j.cast ht)).val)
    (w cap len : ℕ) (raw : List Bool) : Advice.adviceTape w cap len raw x = Advice.adviceTape w cap len raw y := by
  subst b; subst zb
  have eq : x=y := funext fun j => Fin.ext (he j)
  rw [eq]

/-- The literal native advice tape is the diagonal program's distributed advice. -/
theorem nativeAdvice_eq (raw : List Bool) :
    Advice.adviceTape (D.geometry n).w (n^D.constants.prefixPower) (n^D.constants.advicePower)
      raw (nativeOrdinalWords D B denseCount) = D.distributedAdvice B n C raw :=
  tape_congr denseCount (congrArg (Nat.clog 2) (denseCount.trans (FixedRows.labelOrder_length B.Entry n C)))
    _ _ (nativeOrdinal_value D B denseCount) _ _ _ _

private theorem runtime_congr {a b za zb : ℕ} (ht : a=b) (hz : za=zb)
    (x : Fin a → Word za) (y : Fin b → Word zb) (he : ∀ j, (x j).val = (y (j.cast ht)).val) :
    EvaluatorProgramRawInput.runtime x = EvaluatorProgramRawInput.runtime y := by
  subst b; subst zb
  have eq : x=y := funext fun j => Fin.ext (he j)
  rw [eq]

/-- Reading the reindexed exponent field produces the same complete binary
input as `Program.initial` on the model's dense counter values. -/
theorem nativeRuntime_eq (dense : Fin (physicalLabelCount D (n := n)) → Word (physicalCounterWidth D (n := n))) :
    EvaluatorProgramRawInput.runtime (dense ∘ (nativeLabelOrder D B denseCount).symm) =
      EvaluatorProgramRawInput.runtime (D.exponentWords n (B.formalExponents
        (fun j => (dense ((finCongr denseCount).symm j)).val))) := by
  let hf := denseCount.trans (FixedRows.labelOrder_length B.Entry n C)
  apply runtime_congr hf (physicalCounterWidth_eq D)
  intro j
  let i := (nativeLabelOrder D B denseCount).symm j
  change (dense i).val = (dense i).val % (2 ^ D.counterWidth n)
  apply (Nat.mod_eq_of_lt _).symm
  exact (physicalCounterWidth_eq D (n := n)) ▸ (dense i).isLt

variable {hn : 2 ≤ n} {p : Nat.Primes} {model : LabelEvaluator.Model p (B.compressorDegree n) (B.compressorEquations hn C)}
variable (data : D.ScalarData B hn model)

/-- Exact initial state used by the contraction after the middle exponent cut. -/
theorem nativeInitialCode_eq (dense : Fin (physicalLabelCount D (n := n)) → Word (physicalCounterWidth D (n := n))) :
    LiveEvaluatorTail.initialCode (n^D.constants.radiusPower) (UniversalMachine.initial D.evaluator
      (data.raw ++ EvaluatorProgramRawInput.runtime (dense ∘ (nativeLabelOrder D B denseCount).symm))) =
    data.init (fun j => (dense ((finCongr denseCount).symm j)).val) := by
  rw [nativeRuntime_eq]; rfl

/-- A nonempty evaluator has a nonblank tape cell for each input bit. Its
bounded initial configuration therefore fits the whole input in the right
half of the physical window. -/
theorem inputLength_of_fits (p : UniversalMachine.Program) (raw : List Bool) (R : ℕ)
    (running : p.extra ≠ 0) (fit : StateFits R (EvaluatorTail.canonical (UniversalMachine.initial p raw))) :
    raw.length ≤ R+1 := by
  have state : (UniversalMachine.initial p raw).state.val = 2 := by simp [UniversalMachine.initial, running]
  rw [EvaluatorTail.canonical, state, ite_eq_right (by decide), ite_eq_right (by decide)] at fit
  have tape := fit.2.1
  by_contra! h
  have b := tape ((R+1 : ℕ) : ℤ) (.inr (by omega))
  change (Turing.Tape.mk' _ _).nth ((R+1 : ℕ) : ℤ) = 0 at b
  rw [Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD,
    List.getElem?_map,List.getElem?_eq_getElem h] at b
  cases hbit : raw[R+1] <;> simp [hbit] at b

/-- Derive midpoint input space from the verified physical evaluator histories. -/
theorem ScalarData.initialRoom (running : D.evaluator.extra ≠ 0) :
    data.raw.length + (2*(B.compressorLabelCount C n*D.counterWidth n)+6*D.counterWidth n+4) ≤
      n^D.constants.radiusPower+1 := by
  let e := D.exponentWords n (fun _ : Fin (B.compressorLabelCount C n) => 0)
  have space := data.space (fun _ => 0) 0 Fin.elim0 0
  rw [EvaluatorTail.history_zero] at space
  have bound := inputLength_of_fits D.evaluator (data.raw ++ EvaluatorProgramRawInput.runtime e)
    _ running space
  simpa only [List.length_append,EvaluatorProgramRawInput.runtime_length] using bound

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
