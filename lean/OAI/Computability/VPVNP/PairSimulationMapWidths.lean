import OAI.Computability.VPVNP.MotifEntry
import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Native width sums for the inner selector sequence

After a selector is decoded, its width on each supply edge is a fixed table
entry. A private RAM scan over one edge's width cells gives either the field
offset before a copy or the full total checked against the term descriptor.
The scan preserves memory and has a fixed linear instruction count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapWidths

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

private abbrev word (w n : ℕ) : Word w := (n : Word w)

private theorem val_word {n : ℕ} (h : n < 2 ^ w) : (word w n).val = n := Nat.mod_eq_of_lt h

/-- Registers hold cursor, exclusive end, running sum, the constant one and a
temporary width. Each successful iteration consists of four private instructions. -/
def instruction (pc : Fin 4 → Fin p) (reg : Fin 5 ↪ Fin r) (done : Fin p) :
    Fin 4 → Instr w p r k :=
  ![.jumpEq (reg 0) (reg 1) done (pc 1), .loadPrivate (reg 4) (reg 0) (pc 2),
    .binary .add (reg 2) (reg 2) (reg 4) (pc 3), .binary .add (reg 0) (reg 0) (reg 3) (pc 0)]

theorem resize_instruction (pc : Fin 4 → Fin p) (reg : Fin 5 ↪ Fin r) (done : Fin p) (i : Fin 4) :
    (instruction (w := 1) (k := k) pc reg done i).resize w = instruction pc reg done i := by
  fin_cases i <;> rfl

/-- The machine stores the four width-scan instructions at the addresses given by `pc`. -/
def Linked (M : Machine w p r k) (pc : Fin 4 → Fin p) (reg : Fin 5 ↪ Fin r) (done : Fin p) :=
  ∀ i, M.code (pc i) = instruction pc reg done i

variable {M : Machine w p r k} {pc : Fin 4 → Fin p} {reg : Fin 5 ↪ Fin r} {done : Fin p}

private theorem step_at (hl : Linked M pc reg done) (i : Fin 4) {c : Config w p r}
    (hc : c.pc = pc i) :
    M.program.step c = (instruction pc reg done i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

private theorem body (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (hne : c.reg (reg 0) ≠ c.reg (reg 1)) (src x : ℕ) (hs : c.reg (reg 0) = word w src)
    (hx : c.privateMem (word w src) = word w x) (h1 : c.reg (reg 3) = 1) :
    ∃ out, Prefix M c (List.replicate 4 .tick) out ∧ out.pc = pc 0 ∧
      out.reg (reg 0) = word w (src + 1) ∧ out.reg (reg 2) = c.reg (reg 2) + word w x ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 2 → j ≠ reg 4 → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let c₁ := {c with pc := pc 1}
  let c₂ := c₁.put (pc 2) (reg 4) (word w x)
  let c₃ := c₂.put (pc 3) (reg 2) (c.reg (reg 2) + word w x)
  let out := c₃.put (pc 0) (reg 0) (word w (src + 1))
  have s₀ : M.program.step c = .localStep c₁ := by
    rw [step_at hl 0 hc]
    simp [instruction, Instr.run, hne, c₁]
  have s₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step_at hl 1 rfl]
    change CallAction.localStep (c₁.put (pc 2) (reg 4) (c.privateMem (c.reg (reg 0)))) = _
    rw [hs, hx]
  have s₂ : M.program.step c₂ = .localStep c₃ := by
    rw [step_at hl 2 rfl]
    change CallAction.localStep (c₂.put (pc 3) (reg 2) (c₂.reg (reg 2) + c₂.reg (reg 4))) = _
    simp [c₃, c₂, c₁, Config.put]
  have s₃ : M.program.step c₃ = .localStep out := by
    rw [step_at hl 3 rfl]
    change CallAction.localStep (c₃.put (pc 0) (reg 0) (c₃.reg (reg 0) + c₃.reg (reg 3))) = _
    simp [out, c₃, c₂, c₁, Config.put, hs, h1, word]
  refine ⟨out, .tick s₀ (.tick s₁ (.tick s₂ (.tick s₃ (.nil _)))), rfl, by simp [out],
    by simp [out, c₃, Config.put], ?_, rfl, rfl⟩
  intro j h₀ h₂ h₄
  simp [out, c₃, c₂, c₁, Config.put, Function.update_of_ne, h₀, h₂, h₄]

/-- The loop scans the given resident widths, including an empty prefix.
Its register result is the machine-word sum and its instruction count is
independent of all widths and all other memory cells. -/
theorem accumulate (hl : Linked M pc reg done) {n : ℕ} (x : Fin n → ℕ) (src : ℕ)
    (c : Config w p r) (hc : c.pc = pc 0) (hsrc : c.reg (reg 0) = word w src)
    (hend : c.reg (reg 1) = word w (src + n)) (hfit : src + n < 2 ^ w)
    (h1 : c.reg (reg 3) = 1)
    (mem : ∀ j : Fin n, c.privateMem (word w (src + j.val)) = word w (x j)) :
    ∃ out, Prefix M c (List.replicate (4 * n + 1) .tick) out ∧ out.pc = done ∧
      out.reg (reg 2) = c.reg (reg 2) + word w (∑ j, x j) ∧
      out.reg (reg 0) = word w (src + n) ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 2 → j ≠ reg 4 → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  induction n generalizing src c with
  | zero =>
    have he : c.reg (reg 0) = c.reg (reg 1) := hsrc.trans (by simpa using hend.symm)
    have hs : M.program.step c = .localStep {c with pc := done} := by
      rw [step_at hl 0 hc]
      simp [instruction, Instr.run, he]
    exact ⟨_, .tick hs (.nil _), rfl, by simp [word], hsrc, fun _ _ _ _ ↦ rfl, rfl, rfl⟩
  | succ n ih =>
    have ne : c.reg (reg 0) ≠ c.reg (reg 1) := by
      rw [hsrc, hend]
      intro he
      have h := congrArg Fin.val he
      rw [val_word (by omega : src < 2 ^ w), val_word hfit] at h
      omega
    obtain ⟨mid, pre, hpc, hcur, hacc, other, hmem, hp⟩ :=
      body hl c hc ne src (x 0) hsrc (by simpa using mem 0) h1
    have endEq : src + 1 + n = src + (n + 1) := by omega
    obtain ⟨out, tail, ho, ha, hcur', other', hm', hp'⟩ :=
      ih (fun j ↦ x j.succ) (src + 1) mid hpc hcur
        (by rw [endEq, other, hend] <;> simp) (endEq ▸ hfit)
        (by rw [other, h1] <;> simp) (fun j ↦ by
          rw [hmem, show src + 1 + j.val = src + j.succ.val by simp [Fin.val_succ]; omega]
          exact mem j.succ)
    refine ⟨out, ?_, ho, ?_, endEq ▸ hcur', fun j h₀ h₂ h₄ ↦
      (other' j h₀ h₂ h₄).trans (other j h₀ h₂ h₄), hm'.trans hmem, hp'.trans hp⟩
    · convert pre.append tail using 1
      rw [← List.replicate_add]
      congr 1
      omega
    · rw [ha, hacc, Fin.sum_univ_succ]
      simp [word, add_assoc]

/-- A zeroed accumulator returns the natural prefix total when it fits the
word. This is the offset or total computed by the abstract motif interpreter. -/
theorem widthPrefix_native (hl : Linked M pc reg done) {n : ℕ} (x : Fin n → ℕ) (src : ℕ)
    (c : Config w p r) (hc : c.pc = pc 0) (hsrc : c.reg (reg 0) = word w src)
    (hend : c.reg (reg 1) = word w (src + n)) (hfit : src + n < 2 ^ w)
    (hzero : c.reg (reg 2) = 0) (h1 : c.reg (reg 3) = 1) (htotal : (∑ j, x j) < 2 ^ w)
    (mem : ∀ j : Fin n, c.privateMem (word w (src + j.val)) = word w (x j)) :
    ∃ out, Prefix M c (List.replicate (4 * n + 1) .tick) out ∧ out.pc = done ∧
      (out.reg (reg 2)).val = (MotifEntry.widthPrefix x).1 ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  obtain ⟨out, pre, ho, ha, _, _, hm, hp⟩ := accumulate hl x src c hc hsrc hend hfit h1 mem
  refine ⟨out, pre, ho, ?_, hm, hp⟩
  rw [ha, hzero, zero_add, val_word htotal, MotifEntry.widthPrefix_spec]

end PairSimulation.MapWidths

end VPVNP
end Computability
end OAI
