import OAI.Computability.VPVNP.SliceArithmeticHornerMachine
import OAI.Computability.VPVNP.SliceArithmeticCallClear

/-!
# Ports of the reusable slice-field multiplication call

The external interface uses the same low-degree-first polynomial basis for
both operands. Each limb occupies a full arithmetic register. The internal
Horner machine has disjoint ports so its workspace can be reclaimed on return.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.MultiplyCall

open RAMTape BurstRAM HornerControl
open SliceArithmeticStreamRow (state StreamPort)

/-- Caller ports for the prime, zero-word template, degree markers, reduction polynomial, query
scalar, and accumulator. -/
inductive External where
  | prime | zeroWord | degree | coeff | query | acc
  deriving DecidableEq

instance : Fintype External :=
  ⟨{.prime, .zeroWord, .degree, .coeff, .query, .acc}, by intro x; cases x <;> simp⟩

/-- The stack interface for field multiplication, combining private Horner workspace with the
six caller ports. -/
abbrev Port := HornerControl.Ports ⊕ External

/-- Select arithmetic register `i` inside the multiplication call's Horner workspace. -/
def reg (i : Fin 8) : Port := .inl (.inl (.reg i))

/-- The multiplication workspace's persistent register-width template port. -/
def persistent : Port := .inl (.inl .persistent)

/-- Embed a Horner coefficient-stream port into the multiplication call's private workspace. -/
def localStream (s : StreamPort Extra) : Port := .inl (.inr s)

/-- The caller's packed field parameters and operands, including one unary marker per extension
degree. -/
def external (p e w : ℕ) (coeff query acc : List Bool) : Stacks External
  | .prime => wordBits (Fin.ofNat (2^w) p)
  | .zeroWord => wordBits (0 : BurstRAM.Word w)
  | .degree => List.replicate e true
  | .coeff => coeff
  | .query => query
  | .acc => acc

/-- Clean entry and return boundaries. -/
def clean (io : Stacks External) : Stacks Port := Sum.elim (fun _ => []) io

/-- Combine a Horner register and stream bank with the external stacks of the multiplication
call. -/
def workspace (internal : Stacks HornerControl.Ports) (io : Stacks External) : Stacks Port :=
  Sum.elim internal io

/-- Copy the persistent inputs, the three loop counts and the zero-register templates. -/
def copies : List (Port × Port) :=
  [(.inr .prime, reg 0), (.inr .zeroWord, reg 1), (.inr .zeroWord, reg 2), (.inr .zeroWord, reg 3),
   (.inr .zeroWord, reg 4), (.inr .zeroWord, reg 5), (.inr .zeroWord, reg 6), (.inr .zeroWord, reg 7),
   (.inr .zeroWord, persistent), (.inr .coeff, localStream (.outer .savedCoeff)),
   (.inr .acc, localStream (.outer .savedFactor)), (.inr .degree, localStream (.outer .savedCount)),
   (.inr .degree, localStream (.outer .rounds)), (.inr .degree, localStream (.outer .rows))]

/-- Exactly the occupied internal ports after multiplication. -/
def occupied : List Port :=
  (List.ofFn reg) ++ [persistent, localStream .old, localStream (.outer .savedCoeff),
    localStream (.outer .savedFactor), localStream (.outer .savedCount)]

/-- Replace the caller's accumulator with the finished Horner product and clear the occupied
private stacks. -/
def reclaim : FiniteRoutine Port :=
  ((CallClear.clear (.inr .acc)).followedBy
    (SuccessorFields.prependCopy (localStream .old) (.inr .acc) (localStream .scratch))).followedBy
    (CallClear.cleanup occupied)

private theorem occupied_length : occupied.length = 13 := by simp [occupied]

/-- Copy the output to the caller, erase the old accumulator and reclaim
all local registers and streams. -/
theorem reclaim_runs {p e w : ℕ} (registers : Fin 8 → BurstRAM.Word w)
    (coeff factor result : List Bool) (hc : coeff.length = e*w) (hb : factor.length = e*w)
    (hr : result.length = e*w) :
    let caller := extra coeff factor e [] 0 0
    let internal := state registers (streams result [] [] [] caller)
    ∃ t ≤ (e*w+1) + (5*(e*w)+2) + (13*((e+1)*(w+1)+1)+1), reclaim.Runs t
      (workspace internal (external p e w coeff [] factor))
      (clean (external p e w coeff [] result)) := by
  intro caller internal
  let src := workspace internal (external p e w coeff [] factor)
  let blank := workspace internal (external p e w coeff [] [])
  let target := workspace internal (external p e w coeff [] result)
  have hclear := CallClear.clear_runs (.inr External.acc : Port) src
  have hblank : Function.update src (.inr .acc) [] = blank := by
    funext i
    rcases i with i | i
    · rfl
    · cases i <;> rfl
  rw [hblank, show (src (.inr .acc)).length = e*w from hb] at hclear
  have hcopy := SuccessorFields.prependCopy_runs (localStream .old) (.inr External.acc)
    (localStream .scratch) (by decide) (by decide) (by decide) blank rfl
  have htarget : Function.update blank (.inr .acc) (blank (localStream .old) ++ blank (.inr .acc)) =
      target := by
    funext i
    rcases i with i | i
    · rfl
    · cases i <;> simp [blank, target, workspace, external, localStream, internal, streams, state]
  rw [htarget, show (blank (localStream .old)).length = e*w from hr] at hcopy
  have hlen (i : Port) (hi : i ∈ occupied) : (target i).length ≤ (e+1)*(w+1) := by
    simp only [occupied, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ⟨j, rfl⟩ | rfl | rfl | rfl | rfl | rfl <;>
      simp [target, workspace, internal, state, reg, persistent, localStream, ISA.bank, streams,
        caller, extra, hc, hb, hr] <;> nlinarith
  obtain ⟨n, hn, hclean⟩ := CallClear.cleanup_runs occupied target ((e+1)*(w+1)) hlen
  have finalEq : CallClear.erased occupied target = clean (external p e w coeff [] result) := by
    funext i
    rcases i with (k | k) | k
    · cases k with
      | reg i =>
        have hi : reg i ∈ occupied := List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
        unfold CallClear.erased
        dsimp only [reg] at hi
        rw [ite_eq_left hi]
        rfl
      | pub i => exact i.elim0
      | work i => simp [CallClear.erased, occupied, reg, persistent, localStream, target, workspace, internal, state, ISA.bank, clean]
      | persistent => simp [CallClear.erased, occupied, persistent, clean]
      | logPort i =>
        cases i <;> simp [CallClear.erased, occupied, reg, persistent, localStream, target, workspace, internal, state,
          ISA.bank, ISA.logStacks, clean, AddressLog.keys, AddressLog.values]
    · cases k with
      | outer x => cases x <;> simp [CallClear.erased, occupied, reg, persistent, localStream, target, workspace,
          internal, state, streams, caller, extra, clean]
      | _ => simp [CallClear.erased, occupied, reg, persistent, localStream, target, workspace, internal, state, streams, clean]
    · simp [CallClear.erased, occupied, reg, persistent, localStream, target, workspace, clean]
  rw [finalEq] at hclean
  rw [occupied_length] at hn
  exact ⟨_, by omega, (hclear.followedBy hcopy).followedBy hclean⟩

end SliceArithmetic.MultiplyCall

end VPVNP
end Computability
end OAI
