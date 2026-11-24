import OAI.Computability.VPVNP.CompressorRecordRegisterSetup
import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Register recipes reading the private call descriptor

The existing straight-line recipe compiler assigns disjoint outputs and
reuses a bounded scratch bank. For a map call its loads read private memory
at addresses computed from the live descriptor pointer. Every instruction
therefore contributes one tick and both memories are preserved.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapInitCompiler

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedStackRAM
open CompressorRecords CompressorRecords.RowRecipe CompressorRecords.PhaseRecipe
open private emit_list from OAI.Computability.VPVNP.CompressorRecordRegisterSetup
open scoped Fin.CommRing

variable {n v w p r k : ℕ}

/-- The recipe evaluator uses natural addresses while the private memory accepts words. -/
def memory (cells : Word w → Word w) : Memory w := fun i ↦ cells (i : Word w)

/-- Retarget the compiler's read instruction to the private memory of the current call. -/
def instruction (bank : Fin v ↪ Fin r) (ptr : Fin r) (a : Assign v 5) (next : Fin p) :
    Instr w p r k :=
  match a.rhs with
  | .read j => .loadPrivate (bank a.dst) (bank j) next
  | _ => RegisterSetup.instruction bank (fun _ ↦ ptr) a next

theorem resize_instruction (bank : Fin v ↪ Fin r) (ptr : Fin r) (a : Assign v 5) (next : Fin p) :
    (instruction (w := 2) (k := k) bank ptr a next).resize w =
      instruction bank ptr a next := by
  obtain ⟨d, rhs⟩ := a
  cases rhs <;> simp only [instruction, RegisterSetup.instruction, Instr.resize,
    Fin.ofNat_val_eq_self]

/-- Installation condition for the private descriptor initializer. At each indexed program
counter the machine contains the compiled assignment with the next index as its successor. -/
def Linked (bank : Fin v ↪ Fin r) (ptr : Fin r) (M : Machine w p r k) (pc : ℕ → Fin p)
    (lines : List (Assign v 5)) : Prop :=
  ∀ i : Fin lines.length, M.code (pc i.val) = instruction bank ptr lines[i.val] (pc (i.val + 1))

private theorem execute_lines (bank : Fin v ↪ Fin r) (ptr : Fin r) (safe : ∀ i, bank i ≠ ptr)
    (M : Machine w p r k) (pc : ℕ → Fin p) (lines : List (Assign v 5))
    (hl : Linked bank ptr M pc lines) (c : Config w p r) (hc : c.pc = pc 0) :
    let s := c.reg ptr
    let vals := (evaluate (fun _ ↦ s) s (memory c.privateMem) lines (c.reg ∘ bank)).2
    ∃ d, Prefix M c (List.replicate lines.length .tick) d ∧ d.pc = pc lines.length ∧
      (∀ i, d.reg (bank i) = vals i) ∧ (∀ a, (∀ i, a ≠ bank i) → d.reg a = c.reg a) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  induction lines generalizing pc c with
  | nil => exact ⟨c, .nil _, hc, fun _ ↦ rfl, fun _ _ ↦ rfl, rfl, rfl⟩
  | cons a lines ih =>
    let val := a.rhs.value (fun _ ↦ c.reg ptr) (c.reg ptr) (memory c.privateMem) (c.reg ∘ bank)
    let mid := c.put (pc 1) (bank a.dst) val
    have hs : M.program.step c = .localStep mid := by
      have h := hl ⟨0, by simp⟩
      change M.code (pc 0) = instruction bank ptr a (pc 1) at h
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, hc, h]
      obtain ⟨dst, rhs⟩ := a
      cases rhs <;> first | rfl | simp [instruction, Instr.run, mid, val, RHS.value, memory]
    have hr : mid.reg ∘ bank = Function.update (c.reg ∘ bank) a.dst val := by
      funext i
      by_cases he : i = a.dst <;> simp [mid, Config.put, he]
    have hp : mid.reg ptr = c.reg ptr := Function.update_of_ne (Ne.symm (safe _)) ..
    have tail : Linked bank ptr M (fun i ↦ pc (i + 1)) lines :=
      fun i ↦ hl ⟨i.val + 1, by simp [i.isLt]⟩
    obtain ⟨d, pre, hd, vals, rest, hm, hper⟩ := ih _ tail mid rfl
    refine ⟨d, .tick hs pre, hd, ?_, ?_, hm, hper⟩
    · intro i
      simpa only [evaluate, hp, hr, show mid.privateMem = c.privateMem from rfl, val] using vals i
    · exact fun q hq ↦ (rest q hq).trans (Function.update_of_ne (hq _) ..)

/-- Load a complete finite output vector from a private descriptor. The number of
ticks depends solely on the chosen recipes. Outside registers and all cells survive. -/
theorem native (f : Fin n → Expr) (bank : Fin (RegisterSetup.regCount f) ↪ Fin r)
    (ptr : Fin r) (safe : ∀ i, bank i ≠ ptr) (M : Machine w p r k) (pc : ℕ → Fin p)
    (hl : Linked bank ptr M pc (RegisterSetup.lines f)) (c : Config w p r) (hc : c.pc = pc 0) :
    ∃ d, Prefix M c (List.replicate (RegisterSetup.lines f).length .tick) d ∧
      d.pc = pc (RegisterSetup.lines f).length ∧
      (∀ i, d.reg (bank (RegisterSetup.output f i)) =
        (f i).eval (fun _ ↦ c.reg ptr) (c.reg ptr) (memory c.privateMem)) ∧
      (∀ a, (∀ i, a ≠ bank i) → d.reg a = c.reg a) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  obtain ⟨d, pre, hd, vals, rest, hm, hper⟩ := execute_lines bank ptr safe M pc _ hl c hc
  refine ⟨d, pre, hd, fun i ↦ (vals _).trans ?_, rest, hm, hper⟩
  exact (emit_list f _ _ _ (List.finRange n) _ i).trans (ite_eq_left (List.mem_finRange i))

end PairSimulation.MapInitCompiler

end VPVNP
end Computability
end OAI
