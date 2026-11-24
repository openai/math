import OAI.Computability.VPVNP.PairSimulationMapConsistency

/-!
# Scanning a resident field for the cursor routing constraints

Each unused outgoing word must be zero. The mode determines the additional
test on the used outgoing field. It is skipped at an active launch, clamped
at an inactive successor, and compared with the selected incoming field at
a transit vertex. The scan accumulates differences into a mask and advances
all three cursors through the full field even after a mismatch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteField

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Registers 0–2 are the unused outgoing, used outgoing and selected
incoming cursors. Registers 3–6 are the width, mode, sticky mask and one.
Registers 7–10 are the loop index, zero and two scratch words. -/
def instruction (pc : Fin 15 → Fin p) (reg : Fin 11 ↪ Fin r) (done : Fin p) :
    Fin 15 → Instr w p r k :=
  ![.constant (reg 7) 0 (pc 1), .constant (reg 8) 0 (pc 2),
    .jumpEq (reg 7) (reg 3) done (pc 3), .loadPrivate (reg 9) (reg 0) (pc 4),
    .binary .bitOr (reg 5) (reg 5) (reg 9) (pc 5),
    .jumpEq (reg 4) (reg 8) (pc 11) (pc 6), .loadPrivate (reg 9) (reg 1) (pc 7),
    .jumpEq (reg 4) (reg 6) (pc 10) (pc 8), .loadPrivate (reg 10) (reg 2) (pc 9),
    .binary .bitXor (reg 9) (reg 9) (reg 10) (pc 10),
    .binary .bitOr (reg 5) (reg 5) (reg 9) (pc 11),
    .binary .add (reg 0) (reg 0) (reg 6) (pc 12),
    .binary .add (reg 1) (reg 1) (reg 6) (pc 13),
    .binary .add (reg 2) (reg 2) (reg 6) (pc 14),
    .binary .add (reg 7) (reg 7) (reg 6) (pc 2)]

/-- Resizing each instruction preserves its register operands and jump destinations. -/
theorem resize_instruction (pc : Fin 15 → Fin p) (reg : Fin 11 ↪ Fin r) (done : Fin p)
    (i : Fin 15) :
    (instruction (w := 1) (k := k) pc reg done i).resize w = instruction pc reg done i := by
  fin_cases i <;> rfl

/-- Each site in the machine contains its route-field instruction. -/
def Linked (M : Machine w p r k) (pc : Fin 15 → Fin p) (reg : Fin 11 ↪ Fin r)
    (done : Fin p) : Prop := ∀ i, M.code (pc i) = instruction pc reg done i

/-- The mode word specifies the constraint on the selected outgoing field. -/
def PayloadOK (mode used incoming : Word w) : Prop :=
  if mode = 0 then True else if mode = 1 then used = 0 else used = incoming

/-- Cost of dispatch and comparison for the selected outgoing word. -/
def payloadSteps (mode : Word w) : ℕ := if mode = 0 then 1 else if mode = 1 then 4 else 6

/-- Two setup instructions, a final exit test, and one pass through each word. -/
def steps (mode : Word w) (width : ℕ) : ℕ := (7 + payloadSteps mode) * width + 3

theorem steps_le (mode : Word w) (width : ℕ) : steps mode width ≤ 13 * width + 3 := by
  have h : payloadSteps mode ≤ 6 := by
    unfold payloadSteps
    split <;> (first | decide | split <;> decide)
  exact Nat.add_le_add_right (Nat.mul_le_mul_right width (by omega)) 3

/-- The bits of all three arrays relevant to the current routing mode. -/
def Agrees (mem : Word w → Word w) (mode unused used incoming : Word w) (width : ℕ) : Prop :=
  ∀ j : Fin width, mem (unused + (j.val : Word w)) = 0 ∧
    PayloadOK mode (mem (used + (j.val : Word w))) (mem (incoming + (j.val : Word w)))

/-- The scan preserves the width, mode, constant one and all enclosing registers. -/
def Preserved (reg : Fin 11 ↪ Fin r) (a : Fin r) : Prop :=
  a ≠ reg 0 ∧ a ≠ reg 1 ∧ a ≠ reg 2 ∧ a ≠ reg 5 ∧ a ≠ reg 7 ∧ a ≠ reg 8 ∧
    a ≠ reg 9 ∧ a ≠ reg 10

variable {M : Machine w p r k} {pc : Fin 15 → Fin p} {reg : Fin 11 ↪ Fin r} {done : Fin p}

theorem step_at (hl : Linked M pc reg done) (i : Fin 15) {c : Config w p r}
    (hc : c.pc = pc i) :
    M.program.step c = (instruction pc reg done i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

theorem or_zero (x y : Word w) : BinaryOp.bitOr.eval x y = 0 ↔ x = 0 ∧ y = 0 := by
  have h : (BinaryOp.bitOr.eval x y).val = x.val ||| y.val :=
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow x.isLt y.isLt)
  simp only [Fin.ext_iff, h, Fin.val_zero, Nat.or_eq_zero_iff]

theorem xor_zero (x y : Word w) : BinaryOp.bitXor.eval x y = 0 ↔ x = y := by
  have h : (BinaryOp.bitXor.eval x y).val = x.val ^^^ y.val :=
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.isLt y.isLt)
  rw [Fin.ext_iff, h]
  change x.val ^^^ y.val = 0 ↔ _
  constructor
  · intro he
    apply Fin.ext
    calc
      x.val = (x.val ^^^ y.val) ^^^ y.val := by simp
      _ = y.val := by simp [he]
  · rintro rfl
    simp

private theorem payload (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 5)
    (h1 : c.reg (reg 6) = 1) (h0 : c.reg (reg 8) = 0) :
    ∃ out, Prefix M c (List.replicate (payloadSteps (c.reg (reg 4))) .tick) out ∧ out.pc = pc 11 ∧
      (out.reg (reg 5) = 0 ↔ c.reg (reg 5) = 0 ∧ PayloadOK (c.reg (reg 4))
        (c.privateMem (c.reg (reg 1))) (c.privateMem (c.reg (reg 2)))) ∧
      (∀ a, a ≠ reg 5 → a ≠ reg 9 → a ≠ reg 10 → out.reg a = c.reg a) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  by_cases skip : c.reg (reg 4) = 0
  · let out := {c with pc := pc 11}
    have s₅ : M.program.step c = .localStep out := by
      rw [step_at hl 5 hc]
      change CallAction.localStep
        {c with pc := if c.reg (reg 4) = c.reg (reg 8) then pc 11 else pc 6} = _
      simp [out, skip, h0]
    refine ⟨out, ?_, rfl, by simp [out, PayloadOK, skip], fun _ _ _ _ ↦ rfl, rfl, rfl⟩
    rw [show payloadSteps (c.reg (reg 4)) = 1 by simp [payloadSteps, skip]]
    exact .tick s₅ (.nil _)
  let used := c.privateMem (c.reg (reg 1))
  let c₆ := {c with pc := pc 6}
  let c₇ := c₆.put (pc 7) (reg 9) used
  have s₅ : M.program.step c = .localStep c₆ := by
    rw [step_at hl 5 hc]
    change CallAction.localStep
      {c with pc := if c.reg (reg 4) = c.reg (reg 8) then pc 11 else pc 6} = _
    simp [c₆, skip, h0]
  have s₆ : M.program.step c₆ = .localStep c₇ := step_at hl 6 rfl
  by_cases clamp : c.reg (reg 4) = 1
  · let c₁₀ := {c₇ with pc := pc 10}
    let out := c₁₀.put (pc 11) (reg 5) (BinaryOp.bitOr.eval (c.reg (reg 5)) used)
    have s₇ : M.program.step c₇ = .localStep c₁₀ := by
      rw [step_at hl 7 rfl]
      change CallAction.localStep
        {c₇ with pc := if c₇.reg (reg 4) = c₇.reg (reg 6) then pc 10 else pc 8} = _
      simp [c₁₀, c₇, c₆, Config.put, clamp, h1]
    have s₁₀ : M.program.step c₁₀ = .localStep out := by
      rw [step_at hl 10 rfl]
      change CallAction.localStep (c₁₀.put (pc 11) (reg 5)
        (BinaryOp.bitOr.eval (c₁₀.reg (reg 5)) (c₁₀.reg (reg 9)))) = _
      simp [out, c₁₀, c₇, c₆, Config.put]
    refine ⟨out, ?_, rfl, ?_, ?_, rfl, rfl⟩
    · rw [show payloadSteps (c.reg (reg 4)) = 4 by
        simp only [payloadSteps, ite_eq_right skip, ite_eq_left clamp]]
      exact .tick s₅ (.tick s₆ (.tick s₇ (.tick s₁₀ (.nil _))))
    · simp only [out, Config.put, Function.update_self, or_zero, PayloadOK, ite_eq_right skip,
        ite_eq_left clamp, used]
    · intro a h₅ h₉ _
      simp [out, c₁₀, c₇, c₆, Config.put, Function.update_of_ne, h₅, h₉]
  · let incoming := c.privateMem (c.reg (reg 2))
    let c₈ := {c₇ with pc := pc 8}
    let c₉ := c₈.put (pc 9) (reg 10) incoming
    let diff := BinaryOp.bitXor.eval used incoming
    let c₁₀ := c₉.put (pc 10) (reg 9) diff
    let out := c₁₀.put (pc 11) (reg 5) (BinaryOp.bitOr.eval (c.reg (reg 5)) diff)
    have s₇ : M.program.step c₇ = .localStep c₈ := by
      rw [step_at hl 7 rfl]
      change CallAction.localStep
        {c₇ with pc := if c₇.reg (reg 4) = c₇.reg (reg 6) then pc 10 else pc 8} = _
      simp [c₈, c₇, c₆, Config.put, clamp, h1]
    have s₈ : M.program.step c₈ = .localStep c₉ := by
      rw [step_at hl 8 rfl]
      change CallAction.localStep (c₈.put (pc 9) (reg 10) (c₈.privateMem (c₈.reg (reg 2)))) = _
      simp [c₉, c₈, c₇, c₆, incoming, Config.put]
    have s₉ : M.program.step c₉ = .localStep c₁₀ := by
      rw [step_at hl 9 rfl]
      change CallAction.localStep (c₉.put (pc 10) (reg 9)
        (BinaryOp.bitXor.eval (c₉.reg (reg 9)) (c₉.reg (reg 10)))) = _
      simp [c₁₀, diff, c₉, c₈, c₇, Config.put]
    have s₁₀ : M.program.step c₁₀ = .localStep out := by
      rw [step_at hl 10 rfl]
      change CallAction.localStep (c₁₀.put (pc 11) (reg 5)
        (BinaryOp.bitOr.eval (c₁₀.reg (reg 5)) (c₁₀.reg (reg 9)))) = _
      simp [out, c₁₀, c₉, c₈, c₇, c₆, Config.put]
    refine ⟨out, ?_, rfl, ?_, ?_, rfl, rfl⟩
    · rw [show payloadSteps (c.reg (reg 4)) = 6 by simp [payloadSteps, skip, clamp]]
      exact .tick s₅ (.tick s₆ (.tick s₇ (.tick s₈ (.tick s₉ (.tick s₁₀ (.nil _))))))
    · simp only [out, Config.put, Function.update_self, or_zero, diff, xor_zero, PayloadOK,
        ite_eq_right skip, ite_eq_right clamp, used, incoming]
    · intro a h₅ h₉ h₁₀
      simp [out, c₁₀, c₉, c₈, c₇, c₆, Config.put, Function.update_of_ne, h₅, h₉, h₁₀]

private theorem advance (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 11)
    (h1 : c.reg (reg 6) = 1) :
    ∃ out, Prefix M c (List.replicate 4 .tick) out ∧ out.pc = pc 2 ∧
      out.reg (reg 0) = c.reg (reg 0) + 1 ∧ out.reg (reg 1) = c.reg (reg 1) + 1 ∧
      out.reg (reg 2) = c.reg (reg 2) + 1 ∧ out.reg (reg 7) = c.reg (reg 7) + 1 ∧
      (∀ a, a ≠ reg 0 → a ≠ reg 1 → a ≠ reg 2 → a ≠ reg 7 → out.reg a = c.reg a) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let c₁ := c.put (pc 12) (reg 0) (c.reg (reg 0) + 1)
  let c₂ := c₁.put (pc 13) (reg 1) (c.reg (reg 1) + 1)
  let c₃ := c₂.put (pc 14) (reg 2) (c.reg (reg 2) + 1)
  let out := c₃.put (pc 2) (reg 7) (c.reg (reg 7) + 1)
  have s₀ : M.program.step c = .localStep c₁ := by
    rw [step_at hl 11 hc]
    change CallAction.localStep (c.put (pc 12) (reg 0) (c.reg (reg 0) + c.reg (reg 6))) = _
    rw [h1]
  have s₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step_at hl 12 rfl]
    change CallAction.localStep (c₁.put (pc 13) (reg 1) (c₁.reg (reg 1) + c₁.reg (reg 6))) = _
    simp [c₂, c₁, Config.put, h1]
  have s₂ : M.program.step c₂ = .localStep c₃ := by
    rw [step_at hl 13 rfl]
    change CallAction.localStep (c₂.put (pc 14) (reg 2) (c₂.reg (reg 2) + c₂.reg (reg 6))) = _
    simp [c₃, c₂, c₁, Config.put, h1]
  have s₃ : M.program.step c₃ = .localStep out := by
    rw [step_at hl 14 rfl]
    change CallAction.localStep (c₃.put (pc 2) (reg 7) (c₃.reg (reg 7) + c₃.reg (reg 6))) = _
    simp [out, c₃, c₂, c₁, Config.put, h1]
  refine ⟨out, .tick s₀ (.tick s₁ (.tick s₂ (.tick s₃ (.nil _)))),
    rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp [out, c₃, c₂, c₁, Config.put]
  · simp [out, c₃, c₂, Config.put]
  · simp [out, c₃, Config.put]
  · simp [out]
  · intro a h₀ h₁ h₂ h₇
    simp [out, c₃, c₂, c₁, Config.put, Function.update_of_ne, h₀, h₁, h₂, h₇]

private theorem iteration (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 2)
    (hne : c.reg (reg 7) ≠ c.reg (reg 3)) (h1 : c.reg (reg 6) = 1) (hz : c.reg (reg 8) = 0) :
    ∃ out, Prefix M c (List.replicate (7 + payloadSteps (c.reg (reg 4))) .tick) out ∧
      out.pc = pc 2 ∧ out.reg (reg 0) = c.reg (reg 0) + 1 ∧
      out.reg (reg 1) = c.reg (reg 1) + 1 ∧ out.reg (reg 2) = c.reg (reg 2) + 1 ∧
      out.reg (reg 7) = c.reg (reg 7) + 1 ∧
      (out.reg (reg 5) = 0 ↔ c.reg (reg 5) = 0 ∧ c.privateMem (c.reg (reg 0)) = 0 ∧
        PayloadOK (c.reg (reg 4)) (c.privateMem (c.reg (reg 1))) (c.privateMem (c.reg (reg 2)))) ∧
      out.reg (reg 8) = 0 ∧ (∀ a, Preserved reg a → out.reg a = c.reg a) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let x := c.privateMem (c.reg (reg 0))
  let c₁ := {c with pc := pc 3}
  let c₂ := c₁.put (pc 4) (reg 9) x
  let q := c₂.put (pc 5) (reg 5) (BinaryOp.bitOr.eval (c.reg (reg 5)) x)
  have s₂ : M.program.step c = .localStep c₁ := by
    rw [step_at hl 2 hc]
    simp [instruction, Instr.run, hne, c₁]
  have s₃ : M.program.step c₁ = .localStep c₂ := step_at hl 3 rfl
  have s₄ : M.program.step c₂ = .localStep q := by
    rw [step_at hl 4 rfl]
    change CallAction.localStep
      (c₂.put _ _ (BinaryOp.bitOr.eval (c₂.reg (reg 5)) (c₂.reg (reg 9)))) = _
    simp [q, c₂, c₁, Config.put]
  have first : Prefix M c (List.replicate 3 .tick) q := .tick s₂ (.tick s₃ (.tick s₄ (.nil _)))
  obtain ⟨mid, body, hpc, mask, frame, mem, per⟩ := payload hl q rfl
    (by simp [q, c₂, c₁, Config.put, h1]) (by simp [q, c₂, c₁, Config.put, hz])
  have keep (a : Fin r) (h₅ : a ≠ reg 5) (h₉ : a ≠ reg 9) (h₁₀ : a ≠ reg 10) :
      mid.reg a = c.reg a := by
    rw [frame a h₅ h₉ h₁₀]
    simp [q, c₂, c₁, Config.put, Function.update_of_ne, h₅, h₉]
  obtain ⟨out, incr, ret, r₀, r₁, r₂, r₇, frame', mem', per'⟩ := advance hl mid hpc
    ((keep _ (by simp) (by simp) (by simp)).trans h1)
  have mode : q.reg (reg 4) = c.reg (reg 4) := by simp [q, c₂, c₁, Config.put]
  rw [mode] at body
  refine ⟨out, ?_, ret, ?_, ?_, ?_, ?_, ?_, ?_, ?_, mem'.trans mem, per'.trans per⟩
  · convert (first.append body).append incr using 1
    rw [← List.replicate_add, ← List.replicate_add]
    congr 1
    omega
  · rw [r₀, keep] <;> simp
  · rw [r₁, keep] <;> simp
  · rw [r₂, keep] <;> simp
  · rw [r₇, keep] <;> simp
  · rw [frame' (reg 5) (by simp) (by simp) (by simp) (by simp), mask]
    simp [q, c₂, c₁, Config.put, or_zero, x, and_assoc]
  · rw [frame', keep, hz] <;> simp
  · rintro a ⟨h₀, h₁, h₂, h₅, h₇, _, h₉, h₁₀⟩
    exact (frame' a h₀ h₁ h₂ h₇).trans (keep a h₅ h₉ h₁₀)

private theorem loop (hl : Linked M pc reg done) (n : ℕ) (c : Config w p r) (hc : c.pc = pc 2)
    (hend : c.reg (reg 3) = c.reg (reg 7) + (n : Word w))
    (h1 : c.reg (reg 6) = 1) (hz : c.reg (reg 8) = 0) (hfit : n < 2 ^ w) :
    ∃ out, Prefix M c (List.replicate ((7 + payloadSteps (c.reg (reg 4))) * n + 1) .tick) out ∧
      out.pc = done ∧ out.reg (reg 0) = c.reg (reg 0) + (n : Word w) ∧
      out.reg (reg 1) = c.reg (reg 1) + (n : Word w) ∧
      out.reg (reg 2) = c.reg (reg 2) + (n : Word w) ∧
      (out.reg (reg 5) = 0 ↔ c.reg (reg 5) = 0 ∧ Agrees c.privateMem (c.reg (reg 4))
        (c.reg (reg 0)) (c.reg (reg 1)) (c.reg (reg 2)) n) ∧
      (∀ a, Preserved reg a → out.reg a = c.reg a) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  induction n generalizing c with
  | zero =>
    have he : c.reg (reg 7) = c.reg (reg 3) := by simpa using hend.symm
    have hs : M.program.step c = .localStep {c with pc := done} := by
      rw [step_at hl 2 hc]
      simp [instruction, Instr.run, he]
    exact ⟨_, .tick hs (.nil _), rfl, by simp, by simp, by simp, by simp [Agrees],
      fun _ _ ↦ rfl, rfl, rfl⟩
  | succ n ih =>
    have ne : c.reg (reg 7) ≠ c.reg (reg 3) := by
      rw [hend]
      intro he
      have hz' : ((n + 1 : ℕ) : Word w) = 0 :=
        add_left_cancel (a := c.reg (reg 7)) (by simpa using he.symm)
      have hv := congrArg Fin.val hz'
      change (n + 1) % (2 ^ w) = 0 at hv
      rw [Nat.mod_eq_of_lt hfit] at hv
      omega
    obtain ⟨mid, pre, hpc, hu, hs, hi, hidx, mask, hzero, frame, hmem, hper⟩ :=
      iteration hl c hc ne h1 hz
    have hm : mid.reg (reg 4) = c.reg (reg 4) := frame _ (by simp [Preserved])
    obtain ⟨out, tail, ho, hu', hs', hi', mask', frame', hmem', hper'⟩ :=
      ih mid hpc (by rw [frame _ (by simp [Preserved]), hidx, hend]
                     simp [add_assoc, add_comm (1 : Word w)])
        ((frame _ (by simp [Preserved])).trans h1) hzero (by omega)
    refine ⟨out, ?_, ho, ?_, ?_, ?_, ?_, fun a ha ↦ (frame' a ha).trans (frame a ha),
      hmem'.trans hmem, hper'.trans hper⟩
    · rw [hm] at tail
      convert pre.append tail using 1
      rw [← List.replicate_add, Nat.mul_succ]
      congr 1
      omega
    · simpa [hu, add_assoc, add_comm (1 : Word w)] using hu'
    · simpa [hs, add_assoc, add_comm (1 : Word w)] using hs'
    · simpa [hi, add_assoc, add_comm (1 : Word w)] using hi'
    · rw [mask', mask, hmem, hm, hu, hs, hi]
      simp [Agrees, Fin.forall_fin_succ, Fin.val_succ, add_assoc, add_comm (1 : Word w), and_assoc]

/-- The fixed jump table checks all resident words in the three routed slices.
The pointers may wrap or overlap. The only size restriction ensures that the
width fits in the loop counter. -/
theorem run (hl : Linked M pc reg done) (width : ℕ) (c : Config w p r) (hc : c.pc = pc 0)
    (hwidth : c.reg (reg 3) = (width : Word w)) (h1 : c.reg (reg 6) = 1) (hfit : width < 2 ^ w) :
    ∃ out, Prefix M c (List.replicate (steps (c.reg (reg 4)) width) .tick) out ∧ out.pc = done ∧
      out.reg (reg 0) = c.reg (reg 0) + (width : Word w) ∧
      out.reg (reg 1) = c.reg (reg 1) + (width : Word w) ∧
      out.reg (reg 2) = c.reg (reg 2) + (width : Word w) ∧
      (out.reg (reg 5) = 0 ↔ c.reg (reg 5) = 0 ∧
        Agrees c.privateMem (c.reg (reg 4)) (c.reg (reg 0)) (c.reg (reg 1)) (c.reg (reg 2)) width) ∧
      (∀ a, Preserved reg a → out.reg a = c.reg a) ∧ out.privateMem = c.privateMem ∧
      out.persistent = c.persistent := by
  let q := c.put (pc 1) (reg 7) 0
  let d := q.put (pc 2) (reg 8) 0
  have s₀ : M.program.step c = .localStep q := step_at hl 0 hc
  have s₁ : M.program.step q = .localStep d := step_at hl 1 rfl
  have pre : Prefix M c (List.replicate 2 .tick) d := .tick s₀ (.tick s₁ (.nil _))
  obtain ⟨out, tail, hpc, r₀, r₁, r₂, mask, frame, mem, per⟩ := loop hl width d rfl
    (by simp [d, q, Config.put, hwidth]) (by simp [d, q, Config.put, h1]) (by simp [d]) hfit
  have mode : d.reg (reg 4) = c.reg (reg 4) := by simp [d, q, Config.put]
  rw [mode] at tail
  refine ⟨out, ?_, hpc, ?_, ?_, ?_, ?_, ?_, mem, per⟩
  · convert pre.append tail using 1
    rw [← List.replicate_add]
    congr 1
    unfold steps
    omega
  · simpa [d, q, Config.put] using r₀
  · simpa [d, q, Config.put] using r₁
  · simpa [d, q, Config.put] using r₂
  · simpa [d, q, Config.put] using mask
  · intro a h
    rw [frame a h]
    obtain ⟨_, _, _, _, h₇, h₈, _, _⟩ := h
    simp [d, q, Config.put, Function.update_of_ne, h₇, h₈]

end PairSimulation.RouteField

end VPVNP
end Computability
end OAI
