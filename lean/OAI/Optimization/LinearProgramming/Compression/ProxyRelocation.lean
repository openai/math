import OAI.Optimization.LinearProgramming.FieldTransfer.Execution
import Mathlib.Tactic

/-! Relocation of a block of scalar RAM instructions, including its branches. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

def rebaseInstr (off : ℕ) : Instr → Instr
  | .jump j => .jump (off + j)
  | .branchLT a b yes no => .branchLT a b (off + yes) (off + no)
  | .branchAddrLT a b yes no => .branchAddrLT a b (off + yes) (off + no)
  | op => op

def stateAt {K : Type*} (off : ℕ) (s : State K) : State K := {s with pc := off + s.pc}

theorem exec_rebase {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (off : ℕ) (op : Instr) (s : State K) :
    execInstr (rebaseInstr off op) (stateAt off s) =
      (execInstr op s).map (stateAt off) := by
  cases s with
  | mk pc data index output =>
    cases op
    case branchLT a b yes no =>
      by_cases h : data a < data b <;> simp [rebaseInstr, execInstr, stateAt, h]
    case branchAddrLT a b yes no =>
      by_cases h : index a < index b <;> simp [rebaseInstr, execInstr, stateAt, h]
    all_goals simp [rebaseInstr, stateAt, execInstr, State.putData, State.putIndex, apply_ite,
      Nat.add_assoc]

theorem relocate_run {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {p q : Program} (off : ℕ) (keepHalt : Bool)
    (hlookup : ∀ pc op, p[pc]? = some op → (keepHalt = true ∨ ∀ tag, op ≠ .halt tag) →
      q[off + pc]? = some (rebaseInstr off op))
    {s t : State K} {n : ℕ} (h : runExactly p s n = some t)
    (hh : keepHalt = true ∨ t.output = none) :
    runExactly q (stateAt off s) n = some (stateAt off t) := by
  induction n generalizing t with
  | zero =>
    simp only [runExactly, Option.some.injEq] at h ⊢
    rw [h]
  | succ n ih =>
    change (runExactly p s n).bind (step p) = some t at h
    cases he : runExactly p s n with
    | none => simp [he] at h
    | some u =>
      have hnext : step p u = some t := by simpa [he] using h
      have hgo : u.output = none := by
        cases hu : u.output with
        | none => rfl
        | some tag => simp [step, hu] at hnext
      rw [runExactly, ih he (Or.inr hgo), Option.bind_some]
      cases hop : p[u.pc]? with
      | none => simp [step, hgo, hop] at hnext
      | some op =>
        have hx : execInstr op u = some t := by simpa [step, hgo, hop] using hnext
        have hop' : keepHalt = true ∨ ∀ tag, op ≠ .halt tag := by
          rcases hh with hkeep | hlive
          · exact Or.inl hkeep
          · right; rintro tag rfl
            simp [execInstr] at hx
            rw [← hx] at hlive; cases hlive
        have hfetch := hlookup u.pc op hop hop'
        change step q (stateAt off u) = some (stateAt off t)
        unfold step
        change (match u.output, q[off + u.pc]? with
          | none, some inst => execInstr inst (stateAt off u)
          | _, _ => none) = _
        rw [hgo, hfetch]
        exact (exec_rebase off op u).trans (by rw [hx]; rfl)

end Compression
end LinearProgramming
end Optimization
end OAI
