import OAI.Optimization.LinearProgramming.RAM.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-! Scalar arithmetic expressions and their straight-line execution on the paper's RAM. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Expressions for a layer of an arithmetic circuit. Reads address the
preceding layer, so shared results need not be recomputed. -/
inductive ArithExpr (ι : Type*) where
  | zero
  | one
  | read (i : ι)
  | neg (e : ArithExpr ι)
  | add (a b : ArithExpr ι)
  | mul (a b : ArithExpr ι)

namespace ArithExpr

variable {ι K : Type*}

def eval [Ring K] (v : ι → K) : ArithExpr ι → K
  | .zero => 0
  | .one => 1
  | .read i => v i
  | .neg e => -(e.eval v)
  | .add a b => a.eval v + b.eval v
  | .mul a b => a.eval v * b.eval v

def size : ArithExpr ι → ℕ
  | .zero | .one | .read _ => 1
  | .neg e => e.size + 1
  | .add a b | .mul a b => a.size + b.size + 1

/-- The root is written at `base`. During evaluation of the right child, the
left child's result occupies the protected register immediately below it. -/
def compile (addr : ι → ℕ) (base : ℕ) : ArithExpr ι → Program
  | .zero => [.const base 0]
  | .one => [.const base 1]
  | .read i => [.copy base (addr i)]
  | .neg e => e.compile addr (base + 1) ++ [.const base 0, .sub base base (base + 1)]
  | .add a b => a.compile addr base ++ b.compile addr (base + 1) ++ [.add base base (base + 1)]
  | .mul a b => a.compile addr base ++ b.compile addr (base + 1) ++ [.mul base base (base + 1)]

theorem compile_length_le (e : ArithExpr ι) (addr : ι → ℕ) (base : ℕ) :
    (e.compile addr base).length ≤ 2 * e.size := by
  induction e generalizing base with
  | zero | one | read => simp [compile, size]
  | neg e ih =>
    have := ih (base + 1)
    simp only [compile, List.length_append, List.length_cons, List.length_nil, size]
    omega
  | add a b iha ihb | mul a b iha ihb =>
    have := iha base
    have := ihb (base + 1)
    simp only [compile, List.length_append, List.length_cons, List.length_nil, size]
    omega

end ArithExpr

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Executing a block of fall-through instructions, with the original RAM
dispatcher used for each step. -/
inductive BlockExec : Program → State K → State K → Prop
  | nil (s) : BlockExec [] s s
  | cons {i is s u t} (hlive : s.output = none) (hi : execInstr i s = some u)
      (hpc : u.pc = s.pc + 1) (tail : BlockExec is u t) : BlockExec (i :: is) s t

namespace BlockExec

theorem single {i : Instr} {s u : State K} (hlive : s.output = none)
    (hi : execInstr i s = some u) (hpc : u.pc = s.pc + 1) : BlockExec [i] s u :=
  .cons hlive hi hpc (.nil u)

theorem append {a b : Program} {s u t : State K}
    (h : BlockExec a s u) (g : BlockExec b u t) : BlockExec (a ++ b) s t := by
  induction h with
  | nil => exact g
  | cons hlive hi hpc _ ih => exact .cons hlive hi hpc (ih g)

theorem pc_eq {code : Program} {s t : State K} (h : BlockExec code s t) :
    t.pc = s.pc + code.length := by
  induction h with
  | nil => simp
  | cons hlive hi hpc tail ih => simp only [List.length_cons]; omega

end BlockExec

namespace ArithExpr

variable {ι : Type*}

private theorem put_spec (s : State K) (base : ℕ) (x : K) (i : Instr) (hlive : s.output = none)
    (hi : execInstr i s = some (s.putData base x)) :
    ∃ t, BlockExec [i] s t ∧ t.data base = x ∧
      (∀ j < base, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  refine ⟨s.putData base x, .single hlive hi rfl, ?_, ?_, rfl, hlive⟩
  · simp [State.putData]
  · intro j hj
    simp [State.putData, Function.update_of_ne (Nat.ne_of_lt hj)]

private theorem binary_spec (s : State K) (addr : ι → ℕ) (base : ℕ)
    (a b : ArithExpr ι) (op : ℕ → ℕ → ℕ → Instr) (f : K → K → K)
    (hop : ∀ (w : State K) (d i j : ℕ),
      execInstr (op d i j) w = some (w.putData d (f (w.data i) (w.data j))))
    (hfresh : ∀ i, addr i < base)
    (ha : ∃ t, BlockExec (a.compile addr base) s t ∧
      t.data base = a.eval (fun i => s.data (addr i)) ∧
      (∀ j < base, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none)
    (hb : ∀ (u : State K), u.output = none →
      ∃ t, BlockExec (b.compile addr (base+1)) u t ∧
        t.data (base+1) = b.eval (fun i => u.data (addr i)) ∧
        (∀ j < base+1, t.data j = u.data j) ∧ t.index = u.index ∧ t.output = none) :
    ∃ t, BlockExec (a.compile addr base ++ b.compile addr (base+1) ++ [op base base (base+1)]) s t ∧
      t.data base = f (a.eval (fun i => s.data (addr i))) (b.eval (fun i => s.data (addr i))) ∧
      (∀ j < base, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  obtain ⟨u, hu, hleft, huf, hui, huo⟩ := ha
  obtain ⟨v, hv, hright, hvf, hvi, hvo⟩ := hb u huo
  let w := v.putData base (f (v.data base) (v.data (base+1)))
  have hw : BlockExec [op base base (base+1)] v w := .single hvo (hop ..) rfl
  have hin : (fun i => u.data (addr i)) = (fun i => s.data (addr i)) := funext fun i => huf _ (hfresh i)
  refine ⟨w, (hu.append hv).append hw, ?_, ?_, hvi.trans hui, hvo⟩
  · simp [w, State.putData, hvf base (Nat.lt_succ_self _), hleft, hright, hin]
  · intro j hj
    simp [w, State.putData, Function.update_of_ne (Nat.ne_of_lt hj),
      hvf j (Nat.lt_succ_of_lt hj), huf j hj]

/-- Correctness, preservation of all lower registers, and preservation of the
complete index bank. No source address may overlap the scratch area. -/
theorem compile_spec (e : ArithExpr ι) (addr : ι → ℕ) (base : ℕ) (s : State K)
    (hlive : s.output = none) (hfresh : ∀ i, addr i < base) :
    ∃ t, BlockExec (e.compile addr base) s t ∧
      t.data base = e.eval (fun i => s.data (addr i)) ∧
      (∀ j < base, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  induction e generalizing base s with
  | zero => exact put_spec s base 0 (.const base 0) hlive (by simp [execInstr])
  | one => exact put_spec s base 1 (.const base 1) hlive (by simp [execInstr])
  | read i => exact put_spec s base _ (.copy base (addr i)) hlive rfl
  | neg e ih =>
    obtain ⟨u, hu, he, huf, hui, huo⟩ := ih (base+1) s hlive (fun i => Nat.lt_succ_of_lt (hfresh i))
    let v := u.putData base 0
    let w := v.putData base (v.data base - v.data (base+1))
    have hv : BlockExec [.const base 0] u v := .single huo (by simp [v, execInstr]) rfl
    have hw : BlockExec [.sub base base (base+1)] v w := .single huo rfl rfl
    refine ⟨w, hu.append (hv.append hw), ?_, ?_, hui, huo⟩
    · simp [w, v, State.putData, he, eval]
    · intro j hj
      simp [w, v, State.putData, Function.update_of_ne (Nat.ne_of_lt hj),
        huf j (Nat.lt_succ_of_lt hj)]
  | add a b iha ihb =>
    exact binary_spec s addr base a b Instr.add (· + ·) (fun _ _ _ _ => rfl) hfresh
      (iha base s hlive hfresh) (fun u h => ihb (base+1) u h fun i => Nat.lt_succ_of_lt (hfresh i))
  | mul a b iha ihb =>
    exact binary_spec s addr base a b Instr.mul (· * ·) (fun _ _ _ _ => rfl) hfresh
      (iha base s hlive hfresh) (fun u h => ihb (base+1) u h fun i => Nat.lt_succ_of_lt (hfresh i))

end ArithExpr

end Compression
end LinearProgramming
end Optimization
end OAI
