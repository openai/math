import OAI.Computability.VPVNP.RankCoordinateSelectedAdvice
import OAI.Computability.VPVNP.RankCoordinatePrepare

/-! # Complete preparation of the two determinant queries

The evaluator's two public ordinals determine the source monomial and the
replacement row. The fixed label and Frobenius routines start with the same
advice. Their bounded executions supply the canonical input to each Schur
root for the live operation and pair of ordinals.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace RankQuery.Stack.Coordinate.SelectedAdvice

open RAMTape UniversalCountStack BurstRAM SliceArithmetic Cursor Dispatch NativeReader
open RadicalCertificate.MonomialIndex QueryData SliceMinors

variable {K F : Type} {p e t eqs d w v A S P B : ℕ}

/-- Selects the Frobenius preparation routine on a Frobenius step and the label routine on a
label step. -/
def mode : Operation t → Bool | .label _ => false | .frobenius => true
/-- The zero-based variable index for a label step, with zero as the unary input for a
Frobenius step. -/
def label : Operation t → ℕ | .label j => j | .frobenius => 0

private theorem scale_eq (Q : QueryData t eqs F) (op : Operation t) :
    powers Q (mode op) = PairCall.targetScale Q op := by cases op <;> rfl

private theorem mark_eq (op : Operation t) :
    (if mode op then 0 else label op+1) = PairCall.targetMark op := by cases op <;> rfl

private theorem label_le (op : Operation t) : label op ≤ t := by
  cases op with
  | label j => exact j.isLt.le
  | frobenius => exact Nat.zero_le _

variable [DecidableEq K] [Fintype K]

/-- Compares prefix-rank ports through the underlying Gram scan's register and auxiliary port
tags. -/
local instance : DecidableEq (PrefixPort K) := inferInstanceAs (DecidableEq (ScanPort (GramEngine.Aux K)))
/-- Decides equality of the auxiliary ports used to call the prefix-rank machine. -/
local instance : DecidableEq (PrefixWorkspace.Aux (PrefixPort K)) := fun a b => PrefixWorkspace.instDecidableEqAux a b
/-- Distinguishes the word registers and auxiliary ports of the greedy selector workspace. -/
local instance : DecidableEq (Side K) := inferInstanceAs (DecidableEq (PrefixWords.Port (PrefixWorkspace.Aux (PrefixPort K))))
/-- Compares addresses in the row scan, column scan and direct entry reader of a selected
minor. -/
local instance {J : Type} [DecidableEq J] : DecidableEq (SelectedMinor.Host K J) :=
  inferInstanceAs (DecidableEq (Side K ⊕ (Side K ⊕ J)))
/-- Decides equality of the selected row word, selected column word and auxiliary addresses in
the denominator bank. -/
local instance : DecidableEq (Den K) := fun a b => Submatrix.instDecidableEqWork a b

/-- Compares ports of the determinant, ordinal and unary-label preparation components. -/
local instance : DecidableEq (Parts K) := Prepare.partsDecidable
/-- Compares an advice address by its component port or its Boolean scale selector. -/
local instance : DecidableEq (Advice K) := inferInstanceAs (DecidableEq (Parts K ⊕ Bool))
/-- Distinguishes the writable component addresses from the shared temporary stack. -/
local instance : DecidableEq (Work K) := inferInstanceAs (DecidableEq (Parts K ⊕ Unit))
/-- Decides equality of public reader ports and their private advice or working addresses. -/
local instance : DecidableEq (Prepare.Ports (Den K) (Raw K) (Side K)) :=
  inferInstanceAs (DecidableEq (Reader.Port (Advice K ⊕ Work K)))

variable [Fintype (Parts K)]

/-- Prepares the determinant pair by reading the greedy row ordinal and staging the selected
target arguments for the given operation mode. -/
def machine (read : FiniteRoutine (MacaulayRead.Port K)) (b : Bool) : FiniteRoutine (Prepare.Ports (Den K) (Raw K) (Side K)) :=
  Prepare.machine (OrdinalABI.machine (Select.rows read)) (ArgumentStage.selectedSlot (K := K) (Base := K)) b (D := Den K)

variable [Field F] [DecidableEq F] [Fact p.Prime]

/-- Numerator bank for one live query, with the next coordinate as replacement row and the
current coordinate as source of the powered target. -/
def numAt (c : Vector p e) (Q : QueryData t eqs F) (w v : ℕ) (base : Stacks K)
    (op : Operation t) (cur next : Fin Q.dimension) : Stacks (ArgumentStage.Num (Raw K)) :=
  Replacement.workBank w (digits w (combinedOrdinal Q.equations Q.monomials next)) (Submatrix.workBank [] []
    (ArgumentStage.selectedRaw w v (height Q) (width Q) c base base (targetArgs Q op cur) (TargetRead.literal c v)))

omit [Fintype K] [Fintype (Parts K)] in
theorem prepared_root_ready (c : Vector p e) (Q : QueryData t eqs F) (base : Stacks K)
    {ready : Stacks K → Prop} (hr : ready base) (hn : height Q < 2^w)
    (op : Operation t) (cur next : Fin Q.dimension) :
    let denReady := Submatrix.Ready (SelectedMinor.Ready w v (height Q) (width Q) c base ready)
    let numReady := Replacement.Ready w (combinedOrdinal Q.equations Q.monomials next)
      (Submatrix.Ready (SelectedMinor.Ready w v (height Q) (width Q) c base (directReady c w v (targetArgs Q op cur) ready)))
    GramEngine.Ready w v (order Q) (order Q) c denReady (GramEngine.initial w v (order Q) (order Q) c (den c Q w v base)) ∧
      GramEngine.Ready w v (order Q) (order Q) c numReady (GramEngine.initial w v (order Q) (order Q) c (numAt c Q w v base op cur next)) :=
  ArgumentStage.selected_root_ready w v (height Q) (width Q) (order Q) c (order_lt Q hn) (den c Q w v base)
    ⟨_, SelectedMinor.initial_ready base base hr, rfl⟩ base base hr (targetTemplate Q)
    (combinedOrdinal Q.equations Q.monomials next) (Q.basisIndex cur) (PairCall.targetScale Q op) (PairCall.targetMark op)

variable [NeZero e] [Algebra (ZMod p) F] {c : Vector p e} [Fact (Irreducible (modulus c))]
    [DecidableEq (AdjoinRoot (modulus c))]

/-- Runtime preparation from a reader for the original Macaulay relation
matrix. The returned host and the two original public ordinal words meet
the determinant caller's ABI. -/
theorem prepare_bounded (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (Q : QueryData t eqs F)
    (op : Operation t) (cur next : Fin Q.dimension) (read : FiniteRoutine (MacaulayRead.Port K))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read (baseMatrix φ Q) w v B S ready)
    (ha : ∀ a, ready a → ∀ k, (a k).length ≤ A) (base : Stacks K) (hr : ready base)
    (hrSize : height Q+height Q+(height Q+width Q)*height Q+width Q+8 < 2^d)
    (hw : gramWidth d ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (hword : w ≤ P) (harity : t ≤ P) (hscalar : max P (e*v) ≤ A) (hlabel : label op+1 < 2^w) :
    let M := portBound K d w v e A S
    let R := Select.scanTime K (height Q) d w v e B A S + OrdinalABI.overhead w
    let S₀ := selectorCap K d w v e A S
    let lim := Prepare.peak (Parts K) M (max M t) S₀ (label op) w
    ∃ ticks ≤ Prepare.time (Parts K) (mode op) M R (label op) w, ∃ out : Stacks (Work K),
      out Prepare.scratch = [] ∧
      (∀ i, out (Prepare.root i) = RootInit.template c (order Q) w v (den c Q w v base) (numAt c Q w v base op cur next) i) ∧
      (machine read (mode op)).BoundedRun lim ticks
        (state (List.replicate (label op) true) (digits w cur) (digits w next) [] (selectedAdvice c Q w v base) (fun _ => []))
        (state (List.replicate (label op) true) (digits w cur) (digits w next) [] (selectedAdvice c Q w v base) out) := by
  intro M R S₀ lim
  have hdw : d ≤ w := by
    have hh : 2*d+7 ≤ (2*d+7)*(max widthFactor control.wordFactor+1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    unfold gramWidth at hw
    omega
  have pfit := Nat.pow_le_pow_right (by decide : 0 < 2) hdw
  have hn : height Q < 2^w := by omega
  have hm : width Q < 2^w := by omega
  have selector := (Select.row_correctSpace (baseMatrix φ Q) read hc ha hrSize hw hv base hr).castOrdinal
    (interpretedRank φ Q) (interpretedRow φ Q)
  have widthSide : w ≤ S₀ := (Nat.le_add_right w _).trans ((le_max_left ..).trans (Nat.le_add_right ..))
  obtain ⟨hf₁,hf₂,hf₃,hf₄⟩ := fit (d := d) (S := S) c Q base (ha base hr) hn hm hword harity hscalar hv (label op) cur next
  have ambient : max (label op) M ≤ max M t := max_le ((label_le op).trans (le_max_right ..)) (le_max_left ..)
  obtain ⟨u,hu,out,scratch,hroot,run⟩ := Prepare.machine_bounded (M := M) (A := max M t) Q.equations Q.monomials cur next
    (label op) (mode op) (powers Q) c (order Q) (den c Q w v base) (raw c Q w v base) ArgumentStage.selectedSlot
    (OrdinalABI.machine (Select.rows read)) selector widthSide hn
    (fun s hs => hs ▸ side_length (d := d) (S := S) c Q base (ha base hr) hm) (side c Q w v base) rfl hlabel
    (digits w 0) (length_digits w 0).le (fun i => by fin_cases i <;> exact (length_digits w _).le)
    hf₁ hf₂ hf₃ (fun k => (hf₄ k).trans ambient)
  refine ⟨u,hu,out,scratch,?_,run⟩
  intro i
  rw [hroot]
  unfold raw numAt
  rw [ArgumentStage.selected_after, scale_eq, mark_eq]
  rfl

end RankQuery.Stack.Coordinate.SelectedAdvice

end

end VPVNP
end Computability
end OAI
