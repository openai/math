import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import OAI.Optimization.LinearProgramming.RAM.Basic

/-! Independent statement for Theorem 1.4, online compression of minor logarithms. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace MinorLog

/-- A square submatrix in canonical increasing row and column order. -/
structure Square (r n : ℕ) where
  order : Fin (n + 1)
  rows : Fin order.val → Fin r
  cols : Fin order.val → Fin n
  increasingRows : StrictMono rows
  increasingCols : StrictMono cols

/-- The tag distinguishes the two matrices even if they have identical entries. -/
abbrev RawIndex (d e n : ℕ) := Sum (Square d n) (Square e n)

def minor {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ) :
    RawIndex d e n → ℚ
  | .inl u => (D.submatrix u.rows u.cols).det
  | .inr u => (E.submatrix u.rows u.cols).det

abbrev Index {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ) :=
  {u : RawIndex d e n // minor D E u ≠ 0}

noncomputable def logarithm {d e n : ℕ}
    (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ) (u : Index D E) : ℝ :=
  Real.logb 2 |(minor D E u.val : ℝ)|

def clip (B z : ℝ) : ℝ := max (-B) (min z B)

def threshold (n : ℕ) : ℕ := 100 * (n + 1)^3

def entries {r n : ℕ} (M : Matrix (Fin r) (Fin n) ℚ) : List ℚ :=
  (List.ofFn fun i => List.ofFn fun j => M i j).flatten

/-- A request occupies index registers starting at zero: matrix tag, order,
then that many row indices and column indices. The matrix entries are never
available to the machine as bit strings. -/
def squareWords {r n : ℕ} (tag : ℕ) (u : Square r n) : List ℕ :=
  [tag, u.order.val] ++ List.ofFn (fun i => (u.rows i).val) ++
    List.ofFn (fun j => (u.cols j).val)

def words {d e n : ℕ} : RawIndex d e n → List ℕ
  | .inl u => squareWords 0 u
  | .inr u => squareWords 1 u

/-- Between calls both register files persist. The caller overwrites only the
request prefix and starts the fixed service routine at address zero. -/
def resume (s : RAM.State ℚ) (request : List ℕ) : RAM.State ℚ :=
  { s with pc := 0, index := fun i => request[i]?.getD (s.index i), output := none }

def width (z : ℕ) : ℕ := z.log2 + 1

/-- The response exposes the value and individual bits of its reduced signed
numerator and positive denominator in designated registers. -/
def explicitValue (s : RAM.State ℚ) (q : ℚ) : Prop :=
  s.data 0 = q ∧ s.index 0 = width q.num.natAbs ∧ s.index 1 = width q.den ∧
    s.index 2 = (decide (q.num < 0)).toNat ∧
    (∀ i < width q.num.natAbs, s.index (3 + i) = (q.num.natAbs.testBit i).toNat) ∧
    (∀ i < width q.den, s.index (3 + width q.num.natAbs + i) = (q.den.testBit i).toNat)

def emits (s : RAM.State ℚ) : Option ℚ → Prop
  | none => s.output = some 1
  | some q => s.output = some 0 ∧ explicitValue s q

/-- Every step is an instruction of the finite RAM program, and the size
check ranges over the entire trace and every scalar register. -/
def call (program : RAM.Program) (clock height : ℕ) (s t : RAM.State ℚ) : Prop :=
  ∃ k ≤ clock, ∃ trace : Fin (k + 1) → RAM.State ℚ,
    RAM.Trace program s k trace ∧ trace (Fin.last k) = t ∧
    ∀ i j, RAM.ratBits ((trace i).data j) ≤ height

/-- Response order agrees with request order. Initialization is separate and
a restart is an observable response, leaving the new generator state live. -/
inductive Processes {ι : Type} (encode : ι → List ℕ) (program : RAM.Program)
    (clock height outputBits : ℕ) :
    RAM.State ℚ → List ι → List (ι × Option ℚ) → Prop
  | nil (s) : Processes encode program clock height outputBits s [] []
  | cons {s t : RAM.State ℚ} {u : ι} {us : List ι} {r : Option ℚ}
      {rs : List (ι × Option ℚ)} :
      call program (clock - (encode u).length) height (resume s (encode u)) t →
      (encode u).length ≤ clock →
      emits t r →
      (∀ q, r = some q → RAM.ratBits q ≤ outputBits) →
      Processes encode program clock height outputBits t us rs →
      Processes encode program clock height outputBits s (u :: us) ((u, r) :: rs)

/-- Work backwards from the last event in the prefix. A restart ends exactly
the epoch whose answers must agree with the common assignment. -/
def agreesSinceRestart {ι : Type} (f : ι → ℚ) : List (ι × Option ℚ) → Prop
  | [] => True
  | (_, none) :: _ => True
  | (u, some q) :: rest => f u = q ∧ agreesSinceRestart f rest

def extension {ι : Type} (n exponent : ℕ) (logs : ι → ℝ)
    (history : List (ι × Option ℚ)) : Prop :=
  ∃ f : ι → ℚ, agreesSinceRestart f history.reverse ∧
    (∀ u, |(f u : ℝ)| ≤ (2 : ℝ)^exponent) ∧
    ∀ a : ι →₀ ℤ, a.sum (fun _ c => c.natAbs) ≤ 4 →
      |clip (threshold n) (a.sum (fun u c => (c : ℝ) * (f u : ℝ))) -
        clip (threshold n) (a.sum (fun u c => (c : ℝ) * logs u))| ≤
        (1 / 2 : ℝ)^(threshold n)

def restartCount {ι : Type} (history : List (ι × Option ℚ)) : ℕ :=
  (history.filter (fun r => r.2.isNone)).length

end MinorLog

open MinorLog in
/-- Theorem 1.4. The programs and all polynomial bounds are fixed before the
matrix dimensions and entries. A time bound of the form C(n+1)^k is
equivalent to domination by a fixed polynomial. Quantifying all finite
request lists covers every prefix of every adaptive request stream because
the program has deterministic transitions and retains its state. -/
def OnlineMinorLogCompression : Prop :=
  ∃ init serve : RAM.Program, ∃ C k Cᵣ : ℕ,
  ∀ d e : ℕ, let n := d + e
  ∀ (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ),
    let input := entries D ++ entries E
    let dimBound := C * (n + 1)^k
    let height := C * ((input.map RAM.ratBits).sum + 1)^k
    ∃ ready : RAM.State ℚ,
      call init dimBound height (RAM.start [d,e,n] input) ready ∧ ready.output = some 0 ∧
      ∀ requests : List (Index D E), ∃ replies : List (Index D E × Option ℚ),
        Processes (fun u : Index D E => words u.val) serve dimBound height dimBound
          ready requests replies ∧
        restartCount replies ≤ Cᵣ * n^2 * ((2*n).log2 + 1) ∧
        ∀ j ≤ replies.length, extension n dimBound (logarithm D E) (replies.take j)

end OracleSpec
end LinearProgramming
end Optimization
end OAI
