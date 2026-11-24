import OAI.Computability.VPVNP.PrimedCounterAdminExec
import OAI.Computability.VPVNP.PrimedCounterProgram

/-!
# Deterministic prefixes of scheduled calls

Each dispatch step contributes only ticks, preserves external memory, and
passes a determined register file to the selected continuation. The relation
below records both directions for every successful execution and its full log.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Dispatch

open BurstRAM PrimedStackRAM PrimedInputRAM

variable {w r p : ℕ} {pub : Fin p → Word w} {state : Word w}

/-- Removing a deterministic prefix of `k` ticks gives exactly the executions
of the residual program on its prepared registers. -/
def Pref (pub : Fin p → Word w) (state : Word w) (a : Flow r p) (rs : Regs w r)
    (b : Flow r p) (mid : Regs w r) (k : ℕ) : Prop :=
  ∀ m log out m', Flow.Exec pub state a rs m log out m' ↔
    ∃ es, log = List.replicate k .tick ++ es ∧ Flow.Exec pub state b mid m es out m'

namespace Pref

variable {a b c : Flow r p} {rs mid last : Regs w r} {j k : ℕ}

theorem refl : Pref pub state a rs a rs 0 := by
  intro m log out m'
  simp

theorem trans (h : Pref pub state a rs b mid j) (g : Pref pub state b mid c last k) :
    Pref pub state a rs c last (j+k) := by
  intro m log out m'
  rw [h, List.replicate_add]
  constructor
  · rintro ⟨es, rfl, he⟩
    obtain ⟨fs, rfl, hf⟩ := (g m es out m').mp he
    exact ⟨fs, (List.append_assoc ..).symm, hf⟩
  · rintro ⟨es, rfl, he⟩
    exact ⟨_, List.append_assoc .., (g m _ out m').mpr ⟨es, rfl, he⟩⟩

theorem lines {ops : List (Op r p)} (hn : ops ≠ [])
    (ht : ∀ m, trace pub state ops rs m = some (List.replicate k .tick, mid, m)) :
    Pref pub state (.seq (PrimedStackRAM.lines ops hn) b) rs b mid k := by
  intro m log out m'
  constructor
  · intro h
    cases h with
    | seq h₁ h₂ =>
      have he := (Admin.exec_lines_iff_trace hn).mp h₁
      rw [ht] at he
      obtain ⟨rfl, rfl, rfl⟩ := by simpa only [Option.some.injEq, Prod.mk.injEq] using he
      exact ⟨_, rfl, h₂⟩
  · rintro ⟨es, rfl, he⟩
    exact .seq ((Admin.exec_lines_iff_trace hn).mpr (ht m)) he

theorem line {op : Op r p} (ht : ∀ m, op.effect pub state rs m = some (.tick, mid, m)) :
    Pref pub state (.seq (.line op) b) rs b mid 1 := by
  intro m log out m'
  constructor
  · intro h
    cases h with
    | seq h₁ h₂ =>
      cases h₁ with
      | line he =>
        rw [ht] at he
        obtain ⟨rfl, rfl, rfl⟩ := by simpa only [Option.some.injEq, Prod.mk.injEq] using he
        exact ⟨_, rfl, h₂⟩
  · rintro ⟨es, rfl, he⟩
    exact .seq (.line (ht m)) he

theorem ifLtYes {l q : Fin r} (h : rs l < rs q) :
    Pref pub state (.ifLt l q a b) rs a rs 1 := by
  intro m log out m'
  constructor
  · intro he
    cases he with
    | ifLtYes _ he => exact ⟨_, rfl, he⟩
    | ifLtNo hh _ => contradiction
  · rintro ⟨es, rfl, he⟩
    exact .ifLtYes h he

theorem ifLtNo {l q : Fin r} (h : ¬ rs l < rs q) :
    Pref pub state (.ifLt l q a b) rs b rs 1 := by
  intro m log out m'
  constructor
  · intro he
    cases he with
    | ifLtYes hh _ => contradiction
    | ifLtNo _ he => exact ⟨_, rfl, he⟩
  · rintro ⟨es, rfl, he⟩
    exact .ifLtNo h he

theorem ifEqYes {l q : Fin r} (h : rs l = rs q) :
    Pref pub state (.ifEq l q a b) rs a rs 1 := by
  intro m log out m'
  constructor
  · intro he
    cases he with
    | ifEqYes _ he => exact ⟨_, rfl, he⟩
    | ifEqNo hh _ => contradiction
  · rintro ⟨es, rfl, he⟩
    exact .ifEqYes h he

theorem ifEqNo {l q : Fin r} (h : rs l ≠ rs q) :
    Pref pub state (.ifEq l q a b) rs b rs 1 := by
  intro m log out m'
  constructor
  · intro he
    cases he with
    | ifEqYes hh _ => contradiction
    | ifEqNo _ he => exact ⟨_, rfl, he⟩
  · rintro ⟨es, rfl, he⟩
    exact .ifEqNo h he

end Pref
end PrimedCounter.Dispatch

end VPVNP
end Computability
end OAI
