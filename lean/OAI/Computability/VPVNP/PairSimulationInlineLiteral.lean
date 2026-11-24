import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Native synthesis of a fixed table word

A fixed instruction block loads a natural constant modulo the current word modulus.
Its only literal operands are zero and one. Every block of the same capacity takes the
same number of local steps, including at width zero and after the accumulator wraps.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.InlinePublic

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {p r k w : ℕ}

/-- The first two instructions initialize the unit and accumulator registers. Each
remaining instruction either increments the accumulator or copies it to itself. -/
def literalInstruction (w C value : ℕ) (pc : Fin (C + 3) → Fin p)
    (unit acc : Fin r) (i : Fin (C + 2)) : Instr w p r k :=
  if i.val = 0 then .constant unit 1 (pc i.succ)
  else if i.val = 1 then .constant acc 0 (pc i.succ)
  else if i.val - 2 < value then .binary .add acc acc unit (pc i.succ)
  else .copy acc acc (pc i.succ)

theorem literal_resize (C value : ℕ) (pc : Fin (C + 3) → Fin p)
    (unit acc : Fin r) (i : Fin (C + 2)) :
    (literalInstruction (k := k) 2 C value pc unit acc i).resize w =
      literalInstruction w C value pc unit acc i := by
  unfold literalInstruction
  split <;> rename_i h
  · rfl
  · split <;> rename_i h'
    · rfl
    · split <;> rfl

/-- Executing the constant block uses exactly two initializations and one tick for
each reserved position. It preserves the private memory and every other register. -/
theorem literal_prefix {C value : ℕ} {M : Machine w p r k}
    {pc : Fin (C + 3) → Fin p} {unit acc : Fin r} (hu : unit ≠ acc) (hv : value ≤ C)
    (hc : ∀ i : Fin (C + 2), M.code (pc i.castSucc) =
      literalInstruction w C value pc unit acc i) (c : Config w p r) (hp : c.pc = pc 0) :
    ∃ out, Prefix M c (List.replicate (C + 2) .tick) out ∧
      out.pc = pc (Fin.last (C + 2)) ∧ out.reg acc = (value : Word w) ∧
      (∀ j, j ≠ unit → j ≠ acc → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let row (j : ℕ) (hj : j ≤ C) : Fin (C + 3) := ⟨j + 2, by omega⟩
  let cu := c.put (pc ⟨1, by omega⟩) unit 1
  let mid (j : ℕ) (hj : j ≤ C) :=
    cu.put (pc (row j hj)) acc ((min j value : ℕ) : Word w)
  have he (i : Fin (C + 2)) (a : Config w p r) (hpc : a.pc = pc i.castSucc) :
      M.program.step a = (literalInstruction w C value pc unit acc i).run M.publicData a := by
    simp only [Machine.program, hpc, hc]
  have h0 : M.program.step c = .localStep cu := by
    rw [he (⟨0, by omega⟩ : Fin (C + 2)) c hp]
    rfl
  have h1 : M.program.step cu = .localStep (mid 0 (Nat.zero_le _)) := by
    rw [he (⟨1, by omega⟩ : Fin (C + 2)) cu rfl]
    simp [literalInstruction, mid, row, Instr.run]
    congr 2
  have walk (j : ℕ) (hj : j ≤ C) :
      Prefix M c (List.replicate (j + 2) .tick) (mid j hj) := by
    induction j with
    | zero => exact .tick h0 (.tick h1 (.nil _))
    | succ j ih =>
      have hj' : j ≤ C := by omega
      have s : M.program.step (mid j hj') = .localStep (mid (j + 1) hj) := by
        rw [he (⟨j + 2, by omega⟩ : Fin (C + 2)) _ rfl]
        have h₀ : j + 2 ≠ 0 := by omega
        have h₁ : j + 2 ≠ 1 := by omega
        simp only [literalInstruction, h₀, h₁, ite_false, Nat.add_sub_cancel]
        by_cases h : j < value
        · simp [h, Instr.run, BinaryOp.eval, mid, cu, Config.put, hu,
            min_eq_left h.le, row]
        · have hmin : min (j + 1) value = value := min_eq_right (by omega)
          simp [h, Instr.run, mid, Config.put, min_eq_right (by omega : value ≤ j), hmin, row]
      simpa [List.replicate_succ'] using (ih hj').append (.tick s (.nil _))
  refine ⟨mid C le_rfl, walk C le_rfl, rfl, ?_, ?_, rfl, rfl⟩
  · simp [mid, min_eq_right hv]
  · intro j hju hja
    simp [mid, cu, Config.put, Function.update_of_ne hja, Function.update_of_ne hju]

end PairSimulation.InlinePublic

end VPVNP
end Computability
end OAI
