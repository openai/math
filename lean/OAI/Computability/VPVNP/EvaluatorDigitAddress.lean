import OAI.Computability.VPVNP.TallyConstants
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-!
# Computing an address in the packed radix table

Each of the label rows holds `Z` digits, each of width `ℓ`. Fixed stack code
forms the row-major bit address from unary indices and copies the digit width
for the destructive lookup. The indices and dimensions survive every call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorDigitAddress

open RAMTape RAMTape.Tally

/-- Unary registers for the label and column ordinals, row and digit widths, computed address
and scratch used to locate a radix digit. -/
inductive Port where
  | labelIndex | rounds | columnIndex | width | offset | cellWidth | ordinal | outer | tmp
  deriving DecidableEq

instance : Fintype Port :=
  ⟨{.labelIndex, .rounds, .columnIndex, .width, .offset, .cellWidth, .ordinal, .outer, .tmp},
    by intro k; cases k <;> decide⟩

/-- The physical calculation first forms the cell ordinal, then scales it by
the bit width. All temporary registers are cleared before returning. -/
def addressProgram : Program Port :=
  (Program.mul .labelIndex .rounds .ordinal .outer .tmp (by decide)).seq <|
    (Program.copy .columnIndex .ordinal .tmp (by decide) (by decide) (by decide)).seq <|
    (Program.mul .ordinal .width .offset .outer .tmp (by decide)).seq <|
    (Program.copy .width .cellWidth .tmp (by decide) (by decide) (by decide)).seq <|
    Program.clear .ordinal

/-- The fixed stack routine that computes the starting bit address of a row-major digit cell
and prepares its width for lookup. -/
def addressRoutine : FiniteRoutine Port := .ofRoutine addressProgram.code

/-- Register contents for label i and column j in a row with Z cells of width ℓ, including the
offset and cell-width tallies. -/
def registers (i Z j ℓ o w : ℕ) : State Port
  | .labelIndex => i
  | .rounds => Z
  | .columnIndex => j
  | .width => ℓ
  | .offset => o
  | .cellWidth => w
  | _ => 0

/-- Initial unary registers for one cell. -/
def ready (i Z j ℓ : ℕ) := encode (registers i Z j ℓ 0 0)

/-- Address and width for the packed lookup, alongside the preserved inputs. -/
def result (i Z j ℓ : ℕ) := encode (registers i Z j ℓ ((i*Z+j)*ℓ) ℓ)

/-- Number of stack instructions used to compute the bit address and copy the cell width for
digit (i,j). -/
def addressTicks (i Z j ℓ : ℕ) := i*(5*Z+6) + 5*j + (i*Z+j)*(5*ℓ+8) + 5*ℓ + 9

theorem addressRoutine_runs (i Z j ℓ : ℕ) :
    addressRoutine.Runs (addressTicks i Z j ℓ) (ready i Z j ℓ) (result i Z j ℓ) := by
  let s := registers i Z j ℓ 0 0
  have hr : addressProgram.ready s := by
    simp (config := { decide := true }) [addressProgram, s, registers]
  have he : addressProgram.eval s = registers i Z j ℓ ((i*Z+j)*ℓ) ℓ := by
    funext k
    cases k <;> simp (config := { decide := true }) [addressProgram, s, registers]
  have ht : addressProgram.work s = addressTicks i Z j ℓ := by
    simp (config := { decide := true }) [addressProgram, s, registers, addressTicks]
    ring
  have h := addressProgram.spec s hr
  rw [he, ht] at h
  exact h

/-- The address calculation can be called while the packed table, digit
accumulator, and evaluator state occupy arbitrary other stacks. -/
theorem addressRoutine_runs_framed {K : Type} [DecidableEq K] {p : Port → K}
    (hp : Function.Injective p) {s : Stacks K} {i Z j ℓ : ℕ}
    (hs : ∀ k, s (p k) = ready i Z j ℓ k) :
    (addressRoutine.onPorts p).Runs (addressTicks i Z j ℓ) s
      (Function.update (Function.update s (p .offset) (List.replicate ((i*Z+j)*ℓ) true))
        (p .cellWidth) (List.replicate ℓ true)) := by
  apply addressRoutine.runs_onPorts_framed hp (addressRoutine_runs i Z j ℓ) hs
  · intro k
    cases k <;> simp (config := { decide := true })
      [hp.eq_iff, hs, ready, result, encode, registers]
  · intro k hk
    simp [Function.update_of_ne (hk .cellWidth).symm, Function.update_of_ne (hk .offset).symm]

private theorem ordinal_succ_le {i t j Z : ℕ} (hi : i < t) (hj : j < Z) :
    i*Z+j+1 ≤ t*Z := by
  calc
    i*Z+j+1 ≤ i*Z+Z := by omega
    _ = (i+1)*Z := (Nat.succ_mul i Z).symm
    _ ≤ t*Z := Nat.mul_le_mul_right _ hi

/-- A legal cell occupies an interval contained in the packed table. -/
theorem cell_fits {i t j Z : ℕ} (hi : i < t) (hj : j < Z) (ℓ : ℕ) :
    (i*Z+j)*ℓ+ℓ ≤ t*Z*ℓ := by
  simpa only [Nat.succ_mul] using Nat.mul_le_mul_right ℓ (ordinal_succ_le hi hj)

/-- Every cell address can be prepared in time linear in the size of the
table and its number of cells. This form also applies to width zero. -/
theorem addressTicks_le_cells {i t j Z : ℕ} (hi : i < t) (hj : j < Z) (ℓ : ℕ) :
    addressTicks i Z j ℓ ≤ 19*(t*Z) + 5*(t*Z*ℓ) := by
  have ho := ordinal_succ_le hi hj
  have hf := cell_fits hi hj ℓ
  have hrow : i ≤ i*Z := by simpa using Nat.mul_le_mul_left i (show 1 ≤ Z by omega)
  rw [addressTicks, show i*(5*Z+6) + 5*j + (i*Z+j)*(5*ℓ+8) + 5*ℓ + 9 =
    13*(i*Z+j) + 6*i + 5*((i*Z+j)*ℓ+ℓ) + 9 by ring]
  omega

/-- At positive digit width the uniform cell-address clock is at most
twenty-four times the bit length of the table. -/
theorem addressTicks_le {i t j Z ℓ : ℕ} (hi : i < t) (hj : j < Z) (hℓ : 0 < ℓ) :
    addressTicks i Z j ℓ ≤ 24*(t*Z*ℓ) := by
  have h := addressTicks_le_cells hi hj ℓ
  have hc : t*Z ≤ t*Z*ℓ := by simpa using Nat.mul_le_mul_left (t*Z) hℓ
  omega

private inductive CopyPort where
  | src | dst | tmp
  deriving DecidableEq

private def copyPorts {K : Type} (src dst tmp : K) : CopyPort → K
  | .src => src
  | .dst => dst
  | .tmp => tmp

private def smallCopy : FiniteRoutine CopyPort :=
  .ofRoutine (Program.copy .src .dst .tmp (by decide) (by decide) (by decide)).code

/-- Initialize a loop counter by adding a preserved unary count. -/
def copyCount {K : Type} (src dst tmp : K) : FiniteRoutine K :=
  smallCopy.onPorts (copyPorts src dst tmp)

theorem copyCount_runs {K : Type} [DecidableEq K] (src dst tmp : K)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : Stacks K) (n m : ℕ) (hs : s src = List.replicate n true)
    (hd : s dst = List.replicate m true) (ht : s tmp = []) :
    (copyCount src dst tmp).Runs (5*n+2) s
      (Function.update s dst (List.replicate (m+n) true)) := by
  let p := copyPorts src dst tmp
  let v : State CopyPort := fun k => match k with
    | .src => n | .dst => m | .tmp => 0
  have hp : Function.Injective p := by
    intro a b hab
    cases a <;> cases b <;> simp_all [p, copyPorts]
  have h := copyAdd_runs CopyPort.src .dst .tmp (by decide) (by decide) (by decide) v rfl
  apply smallCopy.runs_onPorts_framed hp h
  · intro k
    cases k <;> assumption
  · intro k
    cases k <;> simp (config := { decide := true })
      [p, copyPorts, v, encode, hsd, hdt.symm, hs, ht]
  · intro k hk
    exact Function.update_of_ne (hk .dst).symm ..

end EvaluatorDigitAddress

end VPVNP
end Computability
end OAI
