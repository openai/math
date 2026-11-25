import OAI.Optimization.LinearProgramming.Contract.AppOracleMachine
import OAI.Optimization.LinearProgramming.OracleSpec.Machine
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent specifications for the extremal amplification and monotone contraction
applications. A query must actually have the advertised shape on every legal transcript. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Contract

open RAM OracleSpec

abbrev Exchanges (M : Type*) := List (M × M)

/-- The oracle may depend on all the earlier messages. Its behavior on malformed input
is unrestricted; a successful implementation has to send well-formed messages. -/
def Respects {M Q A : Type*} (ask : Q → M) (answer : A → M) (valid : Q → A → Prop)
    (oracle : Exchanges M → M → M) : Prop :=
  ∀ past q, ∃ a, oracle past (ask q) = answer a ∧ valid q a

def LegalQuestions {M Q : Type*} (ask : Q → M) (past : Exchanges M) : Prop :=
  ∀ q a, (q,a) ∈ past → ∃ v, ask v = q

/-- `true` means low. The two implications both apply when the endpoint bands overlap. -/
def LabelsExtrema {n : ℕ} (s : Fin n → ℝ) (width : ℚ) (labels : Fin n → Bool) : Prop :=
  ∀ i, ((∀ j, s i ≤ s j + (width : ℝ)) → labels i = true) ∧
       ((∀ j, s j ≤ s i + (width : ℝ)) → labels i = false)

def AllowedExtremalReply {n : ℕ} (hidden : Fin n → ℝ) (ρ : ℚ) (shift : Fin n → ℚ) :
    Option (Fin n → Bool) → Prop
  | none => True
  | some labels => LabelsExtrema (fun i => hidden i + (shift i : ℝ)) ρ labels

def labelScalars {n : ℕ} : Option (Fin n → Bool) → List ℚ
  | none => [0]
  | some v => 1 :: List.ofFn (fun i => if v i then 1 else 0)

def labelBits {n : ℕ} : Option (Fin n → Bool) → Word
  | none => [false]
  | some v => true :: List.ofFn v

def vectorBits {n : ℕ} (q : Fin n → ℚ) : Word := (List.ofFn q).flatMap encodeRat

def ratParameterSize (a b : ℚ) : ℕ := RAM.ratBits a + RAM.ratBits b

def logarithmicSize (ratio : ℚ) : ℕ := Nat.log2 (2 + ⌈ratio⌉₊)

/-- Theorem 9.1. Both finite programs are fixed before all dimensions, scales, hidden
vectors, and adaptive oracles. A defeat flag must be backed by a defeat in the transcript. -/
def ExtremalAmplification : Prop :=
  ∃ (arith : OracleProgram) (bits : BitProgram) (C d : ℕ),
    ∀ (n : ℕ), 0 < n → ∀ (ρ κ : ℚ), 0 < ρ → ρ ≤ κ → ∀ (s : Fin n → ℝ),
    let size := n + logarithmicSize (κ / ρ)
    (∀ o : ScalarOracle ℚ, Respects List.ofFn labelScalars (AllowedExtremalReply s ρ) o →
      arith.ComputesWithin o [n] [ρ,κ] (polyBound C d size) fun h t =>
        LegalQuestions (List.ofFn (n := n) (α := ℚ)) h ∧
        ((t.output = some 0 ∧ ∃ q, (q, [0]) ∈ h) ∨
         (t.output = some 1 ∧ ∃ l : Fin n → Bool, LabelsExtrema s κ l ∧
           ∀ i, t.data i.val = if l i then 1 else 0))) ∧
    (∀ o : WordOracle, Respects vectorBits labelBits (AllowedExtremalReply s ρ) o →
      bits.ComputesWithin o (encodeNat n ++ encodeRat ρ ++ encodeRat κ)
        (polyBound C d (size + ratParameterSize ρ κ)) fun h out =>
        LegalQuestions (vectorBits (n := n)) h ∧
        ((out = [false] ∧ ∃ q, (q,[false]) ∈ h) ∨
          ∃ l, LabelsExtrema s κ l ∧ out = labelBits (some l)))

abbrev Cube (n : ℕ) := Fin n → Set.Icc (0 : ℝ) 1
abbrev RatCube (n : ℕ) := Fin n → Set.Icc (0 : ℚ) 1

def realPoint {n : ℕ} (x : RatCube n) : Cube n := fun i =>
  ⟨((x i).1 : ℝ), by exact_mod_cast (x i).2.1, by exact_mod_cast (x i).2.2⟩

structure Evaluation (n : ℕ) where
  point : RatCube n
  precision : ℕ

/-- Only rational points in the cube may be submitted for evaluation. -/
def realQuestion {n : ℕ} (q : Evaluation n) : List ℝ :=
  q.precision :: List.ofFn (fun i => ((q.point i).1 : ℝ))

def bitQuestion {n : ℕ} (q : Evaluation n) : Word :=
  encodeNat q.precision ++ vectorBits (fun i => (q.point i).1)

def bitApproximation {n : ℕ} (z : Fin n → ℤ) : Word :=
  (List.ofFn z).flatMap (fun a => decide (a < 0) :: encodeNat a.natAbs)

def closeEvaluation {n : ℕ} (F : Cube n → Cube n) (q : Evaluation n) (y : Fin n → ℝ) : Prop :=
  ∀ i, |y i - (F (realPoint q.point) i).1| ≤ (2:ℝ)⁻¹ ^ q.precision

def closeDyadicEvaluation {n : ℕ} (F : Cube n → Cube n) (q : Evaluation n)
    (z : Fin n → ℤ) : Prop :=
  closeEvaluation F q (fun i => (z i : ℝ) * ((2:ℝ)⁻¹ ^ q.precision))

/-- Every requested absolute precision is bounded in bits, even when an answer is zero. -/
def PrecisionBound {n : ℕ} {M : Type*} (ask : Evaluation n → M)
    (budget : ℕ) (past : Exchanges M) : Prop :=
  ∀ sent received, (sent,received) ∈ past → ∃ q, ask q = sent ∧ q.precision ≤ budget

def ApproximatesFixedPoint {n : ℕ} (F : Cube n → Cube n) (ε : ℚ) (y : RatCube n) : Prop :=
  (∃ p, F p = p) ∧ ∀ p, F p = p → ∀ i, |((y i).1 : ℝ) - (p i).1| ≤ (ε : ℝ)

/-- Theorem 9.2. The arithmetic machine handles real evaluations of any prescribed accuracy
(including exact answers). The bit machine uses signed numerators on the requested binary
grid. Bounding both the transcript in bits and the requested precision allows substitution
of any evaluator polynomial in its encoding, query length, and the requested precision. -/
def MonotoneContractionSearch : Prop :=
  ∃ (arith : OracleProgram) (bits : BitProgram) (C d : ℕ),
    ∀ (n : ℕ) (γ ε : ℚ), 0 < γ → γ ≤ 1 → 0 < ε → ε ≤ 1 →
    ∀ F : Cube n → Cube n, Monotone F → LipschitzWith (1-(γ:ℝ)).toNNReal F →
    let size := n + logarithmicSize (1 / (γ*ε))
    let aBudget := polyBound C d size
    let bBudget := polyBound C d (size + ratParameterSize γ ε)
    (∀ o : ScalarOracle ℝ, Respects realQuestion List.ofFn (closeEvaluation F) o →
      arith.ComputesWithin o [n] [(γ:ℝ),(ε:ℝ)] aBudget fun h t =>
        PrecisionBound (realQuestion (n:=n)) aBudget h ∧ t.output = some 0 ∧
        ∃ y, ApproximatesFixedPoint F ε y ∧ ∀ i, t.data i.val = ((y i).1 : ℝ)) ∧
    (∀ o : WordOracle, Respects bitQuestion bitApproximation (closeDyadicEvaluation F) o →
      bits.ComputesWithin o (encodeNat n ++ encodeRat γ ++ encodeRat ε) bBudget fun h out =>
        PrecisionBound (bitQuestion (n:=n)) bBudget h ∧
        ∃ y, ApproximatesFixedPoint F ε y ∧ out = vectorBits (fun i => (y i).1))

end Contract
end LinearProgramming
end Optimization
end OAI
