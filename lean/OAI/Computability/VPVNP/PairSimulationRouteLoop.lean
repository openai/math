import OAI.Computability.VPVNP.PrimedCounterGuessWord
import Mathlib.Algebra.BigOperators.Fin

/-!
# Native counted traversal of cursor routing fields

The field scheduler uses the same three labels for a successor scan, a
phase scan, and the scan of steps within a phase. The body may itself
traverse an inner loop. The traversal theorem counts every test, increment
and body instruction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteLoop

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- The loop resets the index, tests it against the exclusive bound and
advances it after the body. The constant-one register is an input. -/
def instruction (pc : Fin 3 → Fin p) (index bound one : Fin r) (body done : Fin p) :
    Fin 3 → Instr w p r k :=
  ![.constant index 0 (pc 1), .jumpEq index bound done body,
    .binary .add index index one (pc 1)]

theorem resize_instruction (pc : Fin 3 → Fin p) (index bound one : Fin r) (body done : Fin p)
    (i : Fin 3) : (instruction (w := 1) (k := k) pc index bound one body done i).resize w =
      instruction pc index bound one body done i := by fin_cases i <;> rfl

/-- All three loop-control instructions occur in the enclosing machine. -/
def Linked (M : Machine w p r k) (pc : Fin 3 → Fin p) (index bound one : Fin r)
    (body done : Fin p) : Prop := ∀ i, M.code (pc i) = instruction pc index bound one body done i

variable {M : Machine w p r k} {pc : Fin 3 → Fin p} {index bound one : Fin r} {body done : Fin p}

private theorem step_at (hl : Linked M pc index bound one body done) (i : Fin 3) {c : Config w p r}
    (hc : c.pc = pc i) :
    M.program.step c = (instruction pc index bound one body done i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

/-- Run the fixed loop on a body with an exact per-index instruction count.
The invariant may refer to registers, private memory and the processed prefix. -/
theorem run_exact (hl : Linked M pc index bound one body done) (n : ℕ) (cost : Fin n → ℕ)
    (hn : n < 2 ^ w) (I : ℕ → Config w p r → Prop)
    (bound_ok : ∀ i q, I i q → q.reg bound = (n : Word w))
    (retag : ∀ i q dst, I i q → I i { q with pc := dst })
    (visit : ∀ i : Fin n, ∀ q : Config w p r, q.pc = body → q.reg index = (i.val : Word w) →
      I i.val q → ∃ d, Prefix M q (List.replicate (cost i) .tick) d ∧ d.pc = pc 2 ∧
        d.reg index = (i.val : Word w) ∧ d.reg one = 1 ∧
        I (i.val + 1) (d.put (pc 1) index ((i.val + 1 : ℕ) : Word w)))
    (c : Config w p r) (hc : c.pc = pc 0) (init : I 0 (c.put (pc 1) index 0)) :
    ∃ d, Prefix M c (List.replicate (2 + ∑ i, (cost i + 2)) .tick) d ∧
      d.pc = done ∧ d.reg index = (n : Word w) ∧ I n d := by
  have loop (m : ℕ) (hm : m ≤ n) :
      ∃ q, Prefix M c (List.replicate (1 + ∑ i : Fin m, (cost (Fin.castLE hm i) + 2)) .tick) q ∧
        q.pc = pc 1 ∧ q.reg index = (m : Word w) ∧ I m q := by
    induction m with
    | zero =>
      have start : M.program.step c = .localStep (c.put (pc 1) index 0) := step_at hl 0 hc
      refine ⟨_, ?_, rfl, by simp, init⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.add_zero]
      exact .tick start (.nil _)
    | succ m ih =>
      let i : Fin n := ⟨m, hm⟩
      obtain ⟨q, pre, hp, hidx, hI⟩ := ih (Nat.le_of_succ_le hm)
      have ne : q.reg index ≠ q.reg bound := by
        rw [hidx, bound_ok m q hI]
        intro he
        have hv := congrArg Fin.val he
        change m % (2 ^ w) = n % (2 ^ w) at hv
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hn] at hv
        omega
      let entered := {q with pc := body}
      have first : M.program.step q = .localStep entered := by
        rw [step_at hl 1 hp]
        simp [instruction, Instr.run, entered, ne]
      obtain ⟨mid, work, hp', hidx', h1, hnext⟩ :=
        visit i entered rfl hidx (retag m q body hI)
      let next := mid.put (pc 1) index ((m+1 : ℕ) : Word w)
      have bump : M.program.step mid = .localStep next := by
        rw [step_at hl 2 hp']
        change CallAction.localStep (mid.put (pc 1) index (mid.reg index + mid.reg one)) = _
        simp [hidx', h1, next, i]
      refine ⟨next, ?_, rfl, by simp [next], hnext⟩
      have head : Prefix M q (List.replicate 1 .tick) entered := .tick first (.nil _)
      have tail : Prefix M mid (List.replicate 1 .tick) next := .tick bump (.nil _)
      rw [Fin.sum_univ_castSucc]
      convert ((pre.append head).append work).append tail using 1
      rw [← List.replicate_add, ← List.replicate_add, ← List.replicate_add]
      congr 1
      let prev := ∑ j : Fin m, (cost (Fin.castLE (Nat.le_of_succ_le hm) j) + 2)
      change 1 + (prev + (cost i + 2)) = 1 + prev + 1 + cost i + 1
      omega
  obtain ⟨q, pre, hp, hidx, hI⟩ := loop n (le_refl n)
  let out := {q with pc := done}
  have he := hidx.trans (bound_ok n q hI).symm
  have exitStep : M.program.step q = .localStep out := by
    rw [step_at hl 1 hp]
    simp [instruction, Instr.run, he, out]
  have tail : Prefix M q (List.replicate 1 .tick) out := .tick exitStep (.nil _)
  refine ⟨out, ?_, rfl, hidx, retag n q done hI⟩
  convert pre.append tail using 1
  rw [← List.replicate_add]
  congr 1
  simp only [Fin.castLE_refl]
  omega

end PairSimulation.RouteLoop

end VPVNP
end Computability
end OAI
