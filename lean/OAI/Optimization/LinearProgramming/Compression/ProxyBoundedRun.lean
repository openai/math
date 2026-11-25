import OAI.Optimization.LinearProgramming.Compression.ProxyRelocation
import OAI.Optimization.LinearProgramming.Compression.ProxyRegisterBits
import OAI.Optimization.LinearProgramming.Compression.ProxySeriesCost

/-! Composition and relocation of rational execution segments with verified
bounds on all intermediate registers. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

structure RegisterBoundedRun (p : Program) (s : State ℚ) (n : ℕ) (t : State ℚ) (B : ℕ) : Prop where
  execution : runExactly p s n = some t
  bound : ∀ j ≤ n, ∀ u, runExactly p s j = some u → scalarBound B u

namespace RegisterBoundedRun

theorem finalBound {p s n t B} (h : RegisterBoundedRun p s n t B) : scalarBound B t :=
  h.bound n le_rfl t h.execution

theorem append {p s n t B k u C} (h₁ : RegisterBoundedRun p s n t B)
    (h₂ : RegisterBoundedRun p t k u C) : RegisterBoundedRun p s (n+k) u (B+C) := by
  constructor
  · rw [runExactly_add_series, h₁.execution, Option.bind_some]
    exact h₂.execution
  · intro j hj v hv
    by_cases h : j ≤ n
    · intro l; exact (h₁.bound j h v hv l).trans (by omega)
    · rw [show j = n+(j-n) by omega, runExactly_add_series, h₁.execution, Option.bind_some] at hv
      intro l; exact (h₂.bound (j-n) (by omega) v hv l).trans (by omega)

theorem short {p s n t B} (hB : 4 ≤ B)
    (hc : ∀ d q, Instr.const d q ∈ p → ratBits q ≤ B) (hs : scalarBound B s)
    (hr : runExactly p s n = some t) : RegisterBoundedRun p s n t (10^n*B) := by
  refine ⟨hr, ?_⟩
  intro j hj u hu a
  have hp := Nat.pow_le_pow_right (n := 10) (by decide) hj
  exact (scalarSteps_bound hB hc hs hu a).trans (Nat.mul_le_mul_right _ hp)

theorem weaken {p s n t B C} (h : RegisterBoundedRun p s n t B) (hBC : B ≤ C) :
    RegisterBoundedRun p s n t C :=
  ⟨h.execution, fun j hj u hu a => (h.bound j hj u hu a).trans hBC⟩

/-- A block invariant offers the same bound at consecutive boundaries, without
accumulating the bound once per iteration. -/
theorem appendSame {p s n t B k u} (h₁ : RegisterBoundedRun p s n t B)
    (h₂ : RegisterBoundedRun p t k u B) : RegisterBoundedRun p s (n+k) u B := by
  refine ⟨(h₁.append h₂).execution, ?_⟩
  intro j hj v hv
  by_cases h : j ≤ n
  · exact h₁.bound j h v hv
  · rw [show j = n+(j-n) by omega, runExactly_add_series, h₁.execution, Option.bind_some] at hv
    exact h₂.bound (j-n) (by omega) v hv

/-- Relocating a block changes only its program counter. The prefix bound
therefore applies at every instruction of the embedded run. -/
theorem relocate {p q s n t B} (h : RegisterBoundedRun p s n t B) (off : ℕ) (keepHalt : Bool)
    (lookup : ∀ pc op, p[pc]? = some op → (keepHalt = true ∨ ∀ tag, op ≠ .halt tag) →
      q[off+pc]? = some (rebaseInstr off op))
    (hfinal : keepHalt = true ∨ t.output = none) :
    RegisterBoundedRun q (stateAt off s) n (stateAt off t) B := by
  refine ⟨relocate_run off keepHalt lookup h.execution hfinal, ?_⟩
  intro j hj v hv
  obtain ⟨tr, htr, hlast⟩ := (runExactly_iff_trace _).mp h.execution
  let i : Fin (n+1) := ⟨j, by omega⟩
  have hlocal := runExactly_of_trace htr i
  change runExactly p s j = some (tr i) at hlocal
  have hflag : keepHalt = true ∨ (tr i).output = none := by
    by_cases hj' : j = n
    · have hi : i = Fin.last n := Fin.ext hj'
      simpa only [hi, hlast] using hfinal
    · right
      let k : Fin n := ⟨j, by omega⟩
      have hnext := htr.2 k
      change step p (tr i) = some (tr k.succ) at hnext
      cases he : (tr i).output with
      | none => rfl
      | some o => simp [step, he] at hnext
  have hv' := relocate_run off keepHalt lookup hlocal hflag
  have eq := Option.some.inj (hv.symm.trans hv')
  rw [eq]
  exact h.bound j hj (tr i) hlocal

end RegisterBoundedRun

end Compression
end LinearProgramming
end Optimization
end OAI
