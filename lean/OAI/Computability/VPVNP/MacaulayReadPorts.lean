import OAI.Computability.VPVNP.MacaulayRowDispatch
import OAI.Computability.VPVNP.RankQueryGramRead
import OAI.Computability.VPVNP.RoutineSpace

/-! # Row and column ports of the physical Macaulay reader

The first two inputs of the row decoder refer directly to the caller's row
and column stacks. All other registers use a private bank. The six decoded
fields remain in that bank for the selected coefficient routine, while the
caller's addresses and field result stack retain their separate names.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead

open BurstRAM RAMTape MacaulayRowDispatch

variable {K : Type}

/-- Private ports for the row decoder and the coefficient routine embedded in the reader. -/
abbrev Work (K : Type) := Small ⊕ K
/-- Matrix-entry reader ports for the row address, column address, result and private
workspace. -/
abbrev Bus (K : Type) := Port (Work K)

/-- Connect the decoder's first two input registers to the caller's row and column stacks. Its
other ports use the private decoder bank. -/
def route : Small → Bus K
  | .reg r => if r = inReg 0 then .row else if r = inReg 1 then .col else .aux (.inl (.reg r))
  | q => .aux (.inl q)

theorem route_injective : Function.Injective (route (K := K)) := by
  intro a b eq
  cases a <;> cases b <;> simp only [route] at eq ⊢ <;> (try split_ifs at eq) <;> simp_all

/-- The caller has separate stacks for the two addresses. The unused private
aliases therefore carry empty strings. -/
def auxBank {w : ℕ} (rs : Reg → Word w) (base : Stacks K) : Stacks (Work K)
  | .inl (.reg r) => if r = inReg 0 ∨ r = inReg 1 then [] else wordBits (rs r)
  | .inl q => ISA.bank Fin.elim0 (0 : Word w) rs [] q
  | .inr k => base k

/-- Full reader frame with the two incoming addresses installed. -/
def frame {w : ℕ} (rs : Reg → Word w) (result : List Bool) (base : Stacks K) : Stacks (Bus K) :=
  bank w (rs (inReg 0)).val (rs (inReg 1)).val result (auxBank rs base)

private theorem first_ne_second : inReg 0 ≠ inReg 1 := by intro e; have := congrArg Fin.val e; contradiction

theorem frame_route {w : ℕ} (rs : Reg → Word w) (res : List Bool) (s : Stacks K) (q : Small) :
    frame rs res s (route q) = ISA.bank Fin.elim0 (0 : Word w) rs [] q := by
  cases q with
  | reg r =>
    by_cases h : r = inReg 0
    · subst r; simp [frame, bank, route, ISA.bank, UniversalCountStack.digits]
    by_cases h' : r = inReg 1
    · subst r; simp [frame, bank, route, ISA.bank, UniversalCountStack.digits, h]
    · simp [frame, bank, route, auxBank, ISA.bank, h, h']
  | pub | persistent | work | logPort => rfl

private theorem outside {w : ℕ} (rs ss : Reg → Word w) (res : List Bool) (s : Stacks K)
    (z : Bus K) (h : ∀ q, route q ≠ z) : frame rs res s z = frame ss res s z := by
  cases z with
  | row => exact (h (.reg (inReg 0)) (by simp [route])).elim
  | col => exact (h (.reg (inReg 1)) (by simp [route, first_ne_second.symm])).elim
  | result => rfl
  | aux x =>
    rcases x with q | k
    · cases q with
      | reg r =>
        by_cases he : r = inReg 0 ∨ r = inReg 1
        · simp [frame, bank, auxBank, he]
        · exact (h (.reg r) (by simp [route, not_or.mp he])).elim
      | pub a => exact a.elim0
      | persistent => exact (h .persistent rfl).elim
      | work i => exact (h (.work i) rfl).elim
      | logPort i => exact (h (.logPort i) rfl).elim
    · rfl

/-- Physical row dispatch on the ordinary reader ABI. All other ports keep
their actual caller state, including the field result stack. -/
theorem dispatch_runs [DecidableEq K] {w : ℕ} (i j equations pins multiples p : ℕ)
    (bound : ∀ a, inputs i j equations pins multiples a < 2^p) (hw : requiredWidth p ≤ w)
    (rs : Reg → Word w) (hin : ∀ a, (rs (inReg a)).val = inputs i j equations pins multiples a)
    (res : List Bool) (s : Stacks K) :
    ∃ cost ≤ ticks w, ∃ out, (machine.onPorts route).Runs cost (frame rs res s) (frame out res s) ∧
      (∀ a, out (inReg a) = rs (inReg a)) ∧
      ∀ a, (out (outReg a)).val = (address i j equations pins multiples).fields a := by
  obtain ⟨d,hd,out,hrun,hold,hnew⟩ := machine_runs i j equations pins multiples p w bound hw rs hin 0
  exact ⟨d,hd,out,machine.runs_onPorts_framed route_injective hrun (frame_route rs res s)
    (frame_route out res s) (outside out rs res s),hold,hnew⟩

/-- A caller can reset its external addresses without clearing the private
register bank. Only the two aliased registers are affected. -/
def setAddresses {w : ℕ} (rs : Reg → Word w) (i j : ℕ) : Reg → Word w :=
  Function.update (Function.update rs (inReg 0) (Fin.ofNat _ i)) (inReg 1) (Fin.ofNat _ j)

theorem reframe {w : ℕ} (rs : Reg → Word w) (base : Stacks K) (i j : ℕ) (res : List Bool) :
    bank w i j res (auxBank rs base) = frame (setAddresses rs i j) res base := by
  funext z
  cases z with
  | row | col =>
    simp [bank, frame, setAddresses, first_ne_second, UniversalCountStack.digits]
    apply congrArg wordBits
    exact Fin.ext (Nat.mod_mod ..).symm
  | result => rfl
  | aux x =>
    rcases x with q | k
    · cases q with
      | reg r =>
        by_cases e : r = inReg 0 ∨ r = inReg 1
        · simp [frame, bank, auxBank, e]
        · simp [frame, bank, auxBank, setAddresses, (not_or.mp e).1, (not_or.mp e).2]
      | pub | persistent | work | logPort => rfl
    · rfl

end RankQuery.Stack.MacaulayRead

end VPVNP
end Computability
end OAI
