import OAI.Computability.BorderVNP.TransmissionDispatch
import Mathlib.Tactic.IntervalCases

/-! # The transmission interval as a physical memory operation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- Normalize the scratch and directory registers, retaining just the fields needed for
an interval. The table interpreter need not actually initialize these scratch words. -/
def Range.bank (r : Range w) (self : Word w) : Bank w := fun i =>
  match i.val with
  | 0 => self
  | 1 => 1
  | 8 => r.kind
  | 9 => r.teamA
  | 10 => r.teamB
  | 11 => r.width
  | 12 => r.source
  | 13 => r.dstA
  | 14 => r.dstB
  | 15 => r.ordinal
  | 16 => 0
  | _ => 0

/-- Selecting the team-side role only requires the public descriptor and the team number. -/
def Range.selected (r : Range w) (self : Word w) : Option (Option Role) :=
  decision.role (r.bank self)

/-- The expected addressed memory transformation on the selected team. -/
def Range.apply (r : Range w) (self : Word w) (pub : Arg → Word w) (m : Memory w) (bits : ℕ → Bool) : Memory w :=
  (r.selected self).elim m (fun role => finishedMemory role pub (r.bank self) m bits)

/-- The number of payload bits handled by this team. -/
def Range.teamCost (r : Range w) (self : Word w) : ℕ :=
  (r.selected self).elim 0 (fun role => payloadCost role r.width.val)

private theorem fields {r : Range w} {self : Word w} {s : Bank w} (hr : rangeBank s = r)
    (hself : s 0 = self) (h1 : s 1 = 1) (h0 : s 2 = 0) :
    ∀ i : Reg, i = 0 ∨ i = 1 ∨ i = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 15) → s i = r.bank self i := by
  intro i hi
  subst r
  rcases hi with rfl | rfl | rfl | h
  · exact hself
  · exact h1
  · exact h0
  · rcases i with ⟨i,hi⟩
    obtain ⟨hlo,hhi⟩ := h
    interval_cases i <;> rfl

/-- Scratch contents cannot change which interval a team selects. -/
theorem Range.role_eq {r : Range w} {s : Bank w} {self : Word w}
    (hr : rangeBank s = r) (hself : s 0 = self) (h1 : s 1 = 1) (h0 : s 2 = 0) :
    decision.role s = r.selected self := by
  have h := fields hr hself h1 h0
  simp only [Range.selected,decision,Decision.role,h 0 (by decide),h 1 (by decide),
    h 2 (by decide),h 8 (by decide),h 9 (by decide),h 10 (by decide)]

/-- The ideal memory after any number of processed bits is independent of scratch values
and the directory cursors. The endpoint address and source are re-read from the real memory
at that bit. -/
theorem Range.memory_eq {r : Range w} {s : Bank w} {self : Word w}
    (hr : rangeBank s = r) (hself : s 0 = self) (h1 : s 1 = 1) (h0 : s 2 = 0)
    (mode : Role) (pub : Arg → Word w) (m : Memory w) (bits : ℕ → Bool) (k : ℕ) :
    rangeMemory mode pub s m bits k = rangeMemory mode pub (r.bank self) m bits k := by
  have h := fields hr hself h1 h0
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rangeMemory, ih]
    cases mode <;>
      simp only [Role.output,write,endpointNat_eq,Function.update_self,Function.update_of_ne (by decide : (1 : Reg) ≠ 16),
        Function.update_of_ne (by decide : (2 : Reg) ≠ 16),Function.update_of_ne (by decide : (9 : Reg) ≠ 16),
        Function.update_of_ne (by decide : (10 : Reg) ≠ 16),Function.update_of_ne (by decide : (12 : Reg) ≠ 16),
        Function.update_of_ne (by decide : (13 : Reg) ≠ 16),Function.update_of_ne (by decide : (14 : Reg) ≠ 16),
        Function.update_of_ne (by decide : (15 : Reg) ≠ 16),
        h 1 (by decide),h 2 (by decide),h 9 (by decide),h 10 (by decide),h 12 (by decide),
        h 13 (by decide),h 14 (by decide),h 15 (by decide)]

/-- The forward dispatch theorem returns the pure addressed memory transformation of its row. -/
theorem Range.finished_eq {r : Range w} {s : Bank w} {self : Word w} {role : Option Role}
    (hr : rangeBank s = r) (hself : s 0 = self) (h1 : s 1 = 1) (h0 : s 2 = 0)
    (sel : r.selected self = some role) (pub : Arg → Word w) (m : Memory w) (bits : ℕ → Bool) :
    finishedMemory role pub s m bits = r.apply self pub m bits := by
  rw [Range.apply,sel]
  cases role with
  | none => rfl
  | some mode =>
    change rangeMemory mode pub s m bits (s 11).val = rangeMemory mode pub (r.bank self) m bits r.width.val
    rw [Range.memory_eq hr hself h1 h0, show s 11 = r.width from congrArg Range.width hr]

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
