import OAI.Computability.VPVNP.RankCursorPorts
import OAI.Computability.VPVNP.RAMTapePublicExprLog
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.RoutineSpace

/-! # Preparing the depth of the Schur product from a binary matrix dimension

At startup the dimension is present on the row-count stack. The rank scan
copies it into the depth word, then computes its ceiling binary logarithm.
The one-register logarithm uses the cursor's otherwise empty ISA work
stacks and leaves every cursor register available to the first request.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch UniversalCountStack

variable {K : Type}

private def logPort : ISA.Port 1 0 → ScanPort K
  | .reg _ => .depth
  | .pub i => Fin.elim0 i
  | .persistent => .cursor (.isa .persistent)
  | .work i => .cursor (.isa (.work i))
  | .logPort i => .cursor (.isa (.logPort i))

private theorem logPort_inj : Function.Injective (@logPort K) := by
  intro i j h
  cases i with
  | pub i => exact i.elim0
  | reg i => cases j with
    | pub j => exact j.elim0
    | reg j => exact congrArg ISA.Port.reg (Subsingleton.elim i j)
    | persistent | work | logPort => cases h
  | persistent | work | logPort =>
    cases j <;> first | exact Fin.elim0 ‹Fin 0› | simp_all [logPort]

/-- Copy the binary row count to the depth stack and replace the copy by its ceiling base-two
logarithm. -/
def prepareDepth : FiniteRoutine (ScanPort K) :=
  (SuccessorFields.prependCopy .rows .depth .scratch).followedBy
    ((PublicExprLog.code (r := 1) (k := 0) true 0).onPorts logPort)

/-- Step bound for copying a w-bit row count and computing the depth of the balanced Schur
product. -/
def depthClock (w : ℕ) := 5*w + 2 + PublicExprLog.bound w

variable [DecidableEq K]

/-- At normal return the bank contains the computed depth word for the full
rank scan. This also works for dimension zero and for the empty word. -/
theorem prepareDepth_runs {w : ℕ} (n : ℕ) (hn : n < 2^w) (persistent : Word w)
    (rs : Regs Registers.R w) (flags : List Bool) (work : Stacks (Engine.Port K)) :
    ∃ t ≤ depthClock w, prepareDepth.Runs t
      (Function.update (scanBank n persistent rs flags work) ScanPort.depth [])
      (scanBank n persistent rs flags work) := by
  let s := scanBank n persistent rs flags work
  let x : Word w := ⟨n, hn⟩
  let first := Function.update s ScanPort.depth []
  let mid := Function.update s ScanPort.depth (digits w n)
  have hc := SuccessorFields.prependCopy_runs ScanPort.rows ScanPort.depth ScanPort.scratch
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) first rfl
  have runCopy : (SuccessorFields.prependCopy ScanPort.rows ScanPort.depth ScanPort.scratch).Runs
      (5*w+2) first mid := by
    simpa only [first, mid, Function.update_of_ne (show ScanPort.rows ≠ (ScanPort.depth : ScanPort K) by intro he; cases he),
      Function.update_self, List.append_nil, Function.update_idem, s, scanBank, length_digits] using hc
  have hx : digits w n = wordBits x := congrArg wordBits (Fin.ext (Nat.mod_eq_of_lt hn))
  obtain ⟨t,ht,run⟩ := PublicExprLog.runs (r := 1) (k := 0) true 0 Fin.elim0 persistent (fun _ => x) []
  have log : ((PublicExprLog.code (r := 1) (k := 0) true 0).onPorts logPort).Runs t mid s := by
    apply FiniteRoutine.runs_onPorts_framed _ logPort_inj run
    · intro i
      cases i with
      | reg j => exact hx
      | pub j => exact j.elim0
      | persistent | work | logPort => rfl
    · intro i
      cases i with
      | reg j =>
        have he : j = 0 := Subsingleton.elim ..
        subst j
        simp only [s, scanBank, logPort, ISA.bank, Function.update_self, ite_true, x, digits]
      | pub j => exact j.elim0
      | persistent | work | logPort => rfl
    · intro k hk
      have hne : k ≠ ScanPort.depth := fun he => hk (.reg 0) he.symm
      exact (Function.update_of_ne hne ..).symm
  exact ⟨_, Nat.add_le_add_left ht _, runCopy.followedBy log⟩

/-- The startup space is polynomial in word width, with the incoming
engine storage and any previously supplied flag bits counted separately. -/
theorem prepareDepth_bounded {w A : ℕ} (n : ℕ) (hn : n < 2^w) (persistent : Word w)
    (rs : Regs Registers.R w) (flags : List Bool) (work : Stacks (Engine.Port K))
    (hw : ∀ k, (work k).length ≤ A) :
    ∃ t ≤ depthClock w, prepareDepth.BoundedRun (max (max w flags.length) A + depthClock w) t
      (Function.update (scanBank n persistent rs flags work) ScanPort.depth [])
      (scanBank n persistent rs flags work) := by
  obtain ⟨t,ht,run⟩ := prepareDepth_runs n hn persistent rs flags work
  refine ⟨t,ht,spaceRun_of_steps run fun k => Nat.add_le_add ?_ ht⟩
  cases k with
  | cursor j => exact (Registers.bank_length persistent rs flags j).trans (le_max_left ..)
  | engine j => exact (hw j).trans (le_max_right ..)
  | rows => exact (length_digits w n).le.trans ((le_max_left ..).trans (le_max_left ..))
  | depth | scratch => exact Nat.zero_le _

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
