import OAI.Computability.VPVNP.MotifEntry
import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Native comparison of the inner selector arrays

The comparison in Theorem 6.1 reads one resident tag per copy from a port
and its anchor. It accumulates the bitwise OR of their differences. Thus a
later match cannot erase an earlier mismatch, and the same accumulator can
be passed from port to port. The scan takes seven private steps per copy
and one exit test, including for arbitrary inputs to a final-site call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapConsistency

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Registers hold the left cursor, exclusive left end, right cursor,
constant one, difference mask, and two scratch words. -/
def instruction (pc : Fin 7 → Fin p) (reg : Fin 7 ↪ Fin r) (done : Fin p) :
    Fin 7 → Instr w p r k :=
  ![.jumpEq (reg 0) (reg 1) done (pc 1),
    .loadPrivate (reg 5) (reg 0) (pc 2), .loadPrivate (reg 6) (reg 2) (pc 3),
    .binary .bitXor (reg 5) (reg 5) (reg 6) (pc 4),
    .binary .bitOr (reg 4) (reg 4) (reg 5) (pc 5),
    .binary .add (reg 0) (reg 0) (reg 3) (pc 6),
    .binary .add (reg 2) (reg 2) (reg 3) (pc 0)]

theorem resize_instruction (pc : Fin 7 → Fin p) (reg : Fin 7 ↪ Fin r) (done : Fin p) (i : Fin 7) :
    (instruction (w := 1) (k := k) pc reg done i).resize w = instruction pc reg done i := by
  fin_cases i <;> rfl

/-- The enclosing machine embeds every comparison instruction at its designated label. -/
def Linked (M : Machine w p r k) (pc : Fin 7 → Fin p) (reg : Fin 7 ↪ Fin r) (done : Fin p) : Prop :=
  ∀ i, M.code (pc i) = instruction pc reg done i

private theorem difference_zero (mask x y : Word w) :
    BinaryOp.bitOr.eval mask (BinaryOp.bitXor.eval x y) = 0 ↔ mask = 0 ∧ x = y := by
  have hx : (BinaryOp.bitXor.eval x y).val = x.val ^^^ y.val :=
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.isLt y.isLt)
  have ho : (BinaryOp.bitOr.eval mask (BinaryOp.bitXor.eval x y)).val =
      mask.val ||| (BinaryOp.bitXor.eval x y).val :=
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow mask.isLt (BinaryOp.bitXor.eval x y).isLt)
  rw [Fin.ext_iff, ho, hx]
  change (mask.val ||| (x.val ^^^ y.val) = 0) ↔ _
  rw [Nat.or_eq_zero_iff]
  constructor
  · rintro ⟨hm, he⟩
    refine ⟨Fin.ext hm, Fin.ext ?_⟩
    calc
      x.val = (x.val ^^^ y.val) ^^^ y.val := by simp
      _ = y.val := by simp [he]
  · rintro ⟨rfl, rfl⟩
    simp

variable {M : Machine w p r k} {pc : Fin 7 → Fin p} {reg : Fin 7 ↪ Fin r} {done : Fin p}

private theorem step_at (hl : Linked M pc reg done) (i : Fin 7) {c : Config w p r}
    (hc : c.pc = pc i) :
    M.program.step c = (instruction pc reg done i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

/-- The comparison only writes the two cursors, the mask and the two scratch registers. -/
def Frame (reg : Fin 7 ↪ Fin r) (c out : Config w p r) : Prop :=
  ∀ j, j ≠ reg 0 → j ≠ reg 2 → j ≠ reg 4 → j ≠ reg 5 → j ≠ reg 6 → out.reg j = c.reg j

private theorem iteration (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (hne : c.reg (reg 0) ≠ c.reg (reg 1)) (hone : c.reg (reg 3) = 1) :
    ∃ out, Prefix M c (List.replicate 7 .tick) out ∧ out.pc = pc 0 ∧
      out.reg (reg 0) = c.reg (reg 0) + 1 ∧ out.reg (reg 2) = c.reg (reg 2) + 1 ∧
      (out.reg (reg 4) = 0 ↔ c.reg (reg 4) = 0 ∧
        c.privateMem (c.reg (reg 0)) = c.privateMem (c.reg (reg 2))) ∧
      Frame reg c out ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let x := c.privateMem (c.reg (reg 0))
  let y := c.privateMem (c.reg (reg 2))
  let d := BinaryOp.bitXor.eval x y
  let c₁ := {c with pc := pc 1}
  let c₂ := c₁.put (pc 2) (reg 5) x
  let c₃ := c₂.put (pc 3) (reg 6) y
  let c₄ := c₃.put (pc 4) (reg 5) d
  let c₅ := c₄.put (pc 5) (reg 4) (BinaryOp.bitOr.eval (c.reg (reg 4)) d)
  let c₆ := c₅.put (pc 6) (reg 0) (c.reg (reg 0) + 1)
  let out := c₆.put (pc 0) (reg 2) (c.reg (reg 2) + 1)
  have s₀ : M.program.step c = .localStep c₁ := by
    rw [step_at hl 0 hc]
    simp [instruction, Instr.run, hne, c₁]
  have s₁ : M.program.step c₁ = .localStep c₂ := step_at hl 1 rfl
  have s₂ : M.program.step c₂ = .localStep c₃ := by
    rw [step_at hl 2 rfl]
    change CallAction.localStep (c₂.put (pc 3) (reg 6) (c.privateMem (c₂.reg (reg 2)))) = _
    simp [c₃, c₂, c₁, Config.put, y]
  have s₃ : M.program.step c₃ = .localStep c₄ := by
    rw [step_at hl 3 rfl]
    change CallAction.localStep (c₃.put (pc 4) (reg 5)
      (BinaryOp.bitXor.eval (c₃.reg (reg 5)) (c₃.reg (reg 6)))) = _
    simp [c₄, c₃, c₂, d, Config.put]
  have s₄ : M.program.step c₄ = .localStep c₅ := by
    rw [step_at hl 4 rfl]
    change CallAction.localStep (c₄.put (pc 5) (reg 4)
      (BinaryOp.bitOr.eval (c₄.reg (reg 4)) (c₄.reg (reg 5)))) = _
    simp [c₅, c₄, c₃, c₂, c₁, Config.put]
  have s₅ : M.program.step c₅ = .localStep c₆ := by
    rw [step_at hl 5 rfl]
    change CallAction.localStep (c₅.put (pc 6) (reg 0) (c₅.reg (reg 0) + c₅.reg (reg 3))) = _
    simp [c₆, c₅, c₄, c₃, c₂, c₁, Config.put, hone]
  have s₆ : M.program.step c₆ = .localStep out := by
    rw [step_at hl 6 rfl]
    change CallAction.localStep (c₆.put (pc 0) (reg 2) (c₆.reg (reg 2) + c₆.reg (reg 3))) = _
    simp [out, c₆, c₅, c₄, c₃, c₂, c₁, Config.put, hone]
  refine ⟨out, .tick s₀ (.tick s₁ (.tick s₂ (.tick s₃ (.tick s₄ (.tick s₅ (.tick s₆ (.nil _))))))),
    rfl, by simp [out, c₆, Config.put], by simp [out], ?_, ?_, rfl, rfl⟩
  · simpa [out, c₆, c₅, Config.put, d, x, y] using difference_zero (c.reg (reg 4)) x y
  · intro j h₀ h₂ h₄ h₅ h₆
    simp [out, c₆, c₅, c₄, c₃, c₂, c₁, Config.put, Function.update_of_ne, h₀, h₂, h₄, h₅, h₆]

/-- Execute the comparison on two private arrays. They may overlap and their
values need not be valid selector codes. The output mask is zero precisely
when the incoming mask was zero and every compared word agreed. -/
theorem compareArrays (hl : Linked M pc reg done) {n : ℕ} (x y : Fin n → Word w)
    (left right : Word w) (c : Config w p r) (hc : c.pc = pc 0)
    (hleft : c.reg (reg 0) = left) (hend : c.reg (reg 1) = left + (n : Word w))
    (hright : c.reg (reg 2) = right) (h1 : c.reg (reg 3) = 1) (hn : n < 2 ^ w)
    (hx : ∀ i : Fin n, c.privateMem (left + (i.val : Word w)) = x i)
    (hy : ∀ i : Fin n, c.privateMem (right + (i.val : Word w)) = y i) :
    ∃ out, Prefix M c (List.replicate (7 * n + 1) .tick) out ∧ out.pc = done ∧
      out.reg (reg 0) = left + (n : Word w) ∧ out.reg (reg 2) = right + (n : Word w) ∧
      (out.reg (reg 4) = 0 ↔ c.reg (reg 4) = 0 ∧ ∀ i, x i = y i) ∧
      Frame reg c out ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  induction n generalizing left right c with
  | zero =>
    have he : c.reg (reg 0) = c.reg (reg 1) := hleft.trans (by simpa using hend.symm)
    have hs : M.program.step c = .localStep {c with pc := done} := by
      rw [step_at hl 0 hc]
      simp [instruction, Instr.run, he]
    exact ⟨_, .tick hs (.nil _), rfl, by simpa using hleft, by simpa using hright,
      by simp, fun _ _ _ _ _ _ ↦ rfl, rfl, rfl⟩
  | succ n ih =>
    have ne : c.reg (reg 0) ≠ c.reg (reg 1) := by
      rw [hleft, hend]
      intro h
      have hz : ((n + 1 : ℕ) : Word w) = 0 := add_left_cancel (a := left) (by simpa using h.symm)
      have hv := congrArg Fin.val hz
      change (n + 1) % (2 ^ w) = 0 at hv
      rw [Nat.mod_eq_of_lt hn] at hv
      omega
    obtain ⟨mid, pre, hpc, hl', hr', mask, frame, hmem, hp⟩ := iteration hl c hc ne h1
    have htail (base : Word w) (i : Fin n) :
        base + 1 + (i.val : Word w) = base + (i.succ.val : Word w) := by
      simp [Fin.val_succ, add_assoc, add_comm (1 : Word w)]
    obtain ⟨out, tail, ho, hleft', hright', hm, frame', hm', hp'⟩ :=
      ih (fun i ↦ x i.succ) (fun i ↦ y i.succ) (left + 1) (right + 1) mid hpc
        (hl'.trans (by rw [hleft]))
        (by rw [frame, hend] <;> simp [add_assoc, add_comm (1 : Word w)])
        (hr'.trans (by rw [hright])) (by rw [frame, h1] <;> simp) (by omega)
        (fun i ↦ by rw [hmem, htail]; exact hx i.succ)
        (fun i ↦ by rw [hmem, htail]; exact hy i.succ)
    refine ⟨out, ?_, ho, ?_, ?_, ?_, fun j h₀ h₂ h₄ h₅ h₆ ↦
      (frame' j h₀ h₂ h₄ h₅ h₆).trans (frame j h₀ h₂ h₄ h₅ h₆), hm'.trans hmem, hp'.trans hp⟩
    · convert pre.append tail using 1
      rw [← List.replicate_add]
      congr 1
      omega
    · simpa [add_assoc, add_comm (1 : Word w)] using hleft'
    · simpa [add_assoc, add_comm (1 : Word w)] using hright'
    · have hx₀ : c.privateMem left = x 0 := by simpa using hx 0
      have hy₀ : c.privateMem right = y 0 := by simpa using hy 0
      rw [hm, mask, hleft, hright, hx₀, hy₀, Fin.forall_fin_succ, and_assoc]

/-- The two exit instructions test the accumulated difference mask. Each input
takes the same number of ticks, including an unused selector pattern or an
empty sequence. Selector validity is checked by the anchor's table lookup. -/
theorem compareTags {b u : ℕ} (enc : Word b ↪ Word w)
    (hl : Linked M pc reg done) (test yes no : Fin p)
    (hz : M.code done = .constant (reg 5) 0 test)
    (hj : M.code test = .jumpEq (reg 4) (reg 5) yes no)
    (x y : Fin u → Word b) (left right : Word w) (c : Config w p r) (hc : c.pc = pc 0)
    (hleft : c.reg (reg 0) = left) (hend : c.reg (reg 1) = left + (u : Word w))
    (hright : c.reg (reg 2) = right) (h1 : c.reg (reg 3) = 1) (hzero : c.reg (reg 4) = 0)
    (hu : u < 2 ^ w) (hx : ∀ i : Fin u, c.privateMem (left + (i.val : Word w)) = enc (x i))
    (hy : ∀ i : Fin u, c.privateMem (right + (i.val : Word w)) = enc (y i)) :
    ∃ out, Prefix M c (List.replicate (7 * u + 3) .tick) out ∧
      out.pc = (if ∀ i, x i = y i then yes else no) ∧
      Frame reg c out ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  obtain ⟨mid, pre, hm, _, _, mask, frame, hmem, hper⟩ :=
    compareArrays hl (enc ∘ x) (enc ∘ y) left right c hc hleft hend hright h1 hu hx hy
  have he : mid.reg (reg 4) = 0 ↔ ∀ i, x i = y i := by
    simpa [hzero, Function.comp_def] using mask
  let q := mid.put test (reg 5) 0
  let out := {q with pc := if ∀ i, x i = y i then yes else no}
  have s₀ : M.program.step mid = .localStep q := by simp [Machine.program, hm, hz, Instr.run, q]
  have s₁ : M.program.step q = .localStep out := by
    change (M.code test).run M.publicData q = _
    rw [hj]
    simp [Instr.run, out, q, Config.put, he]
  have tail : Prefix M mid (List.replicate 2 .tick) out := .tick s₀ (.tick s₁ (.nil _))
  refine ⟨out, ?_, rfl, ?_, hmem, hper⟩
  · convert pre.append tail using 1
    rw [← List.replicate_add]
  · intro j h₀ h₂ h₄ h₅ h₆
    simpa [out, q, Config.put, Function.update_of_ne h₅] using frame j h₀ h₂ h₄ h₅ h₆

end PairSimulation.MapConsistency

end VPVNP
end Computability
end OAI
