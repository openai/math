import OAI.Computability.VPVNP.RankCursorPorts
import OAI.Computability.VPVNP.RankCursorLoop
import OAI.Computability.VPVNP.SliceArithmeticZero
import OAI.Computability.VPVNP.SliceArithmeticCallClear

/-! # Checking one Schur coefficient and rolling the rank registers

After the root query returns, the zero test scans the field element in its
polynomial-basis representation. Its bit feeds the cursor update directly.
The check erases the coefficient and reuses the same registers on the next
root query.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch

variable {K : Type} [DecidableEq K]

private def zeroPort : SliceArithmeticZero.Port → ScanPort K
  | .input => .engine .result
  | .flag => .cursor .flag
  | .scratch => .scratch

omit [DecidableEq K] in
private theorem zeroPort_injective : Function.Injective (zeroPort (K := K)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [zeroPort]

/-- Consume the scalar result, roll the two binary cursor words, and emit
the control bit for the next iteration. -/
def check : FiniteRoutine (ScanPort K) :=
  (((SliceArithmeticZero.machine.onPorts zeroPort).followedBy
    (SliceArithmetic.CallClear.clear (.engine .result))).followedBy (Registers.next.onPorts .cursor))

/-- Step bound for testing the packed Schur coefficient for zero, clearing the scalar, and
advancing the rank cursor registers. -/
def checkClock (w v e : ℕ) := 5*(e*v) + 4 + Registers.clock w

private theorem zero_test {p e w v : ℕ} [Fact p.Prime]
    {c : SliceArithmetic.Vector p e} (hw : SliceArithmetic.Word.workingWidth p ≤ v)
    (n : ℕ) (persistent : Word w) (rs : Regs Registers.R w) (aux : Stacks K) (a : Scalar c) :
    (SliceArithmeticZero.machine.onPorts zeroPort).Runs (4*(e*v)+3)
      (scanBank n persistent rs [] (yielded aux (Engine.scalar v a)))
      (scanBank n persistent rs [decide (a = 0)] (yielded aux (Engine.scalar v a))) := by
  have hd : a.digits = SliceArithmetic.zero p e ↔ a = 0 := by
    constructor
    · intro h
      change a = Scalar.pack c (SliceArithmetic.zero p e)
      simpa only [Scalar.pack_digits] using congrArg (Scalar.pack c) h
    · rintro rfl
      exact Scalar.digits_pack _
  have h := SliceArithmeticZero.vector_runs hw a.digits []
  simp only [hd] at h
  apply SliceArithmeticZero.machine.runs_onPorts_framed (ports := zeroPort) zeroPort_injective h
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro k hk
    cases k with
    | cursor k => cases k with
      | isa j => rfl
      | flag => exact (hk .flag rfl).elim
    | _ => rfl

/-- The rank registers and the entire engine bank are reusable after the
scalar check, including the full polynomial-basis zero test in characteristic two. -/
theorem check_runs {p e w v b : ℕ} [Fact p.Prime]
    {c : SliceArithmetic.Vector p e} (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (n Z u z : ℕ) (persistent : Word w) (rs : Regs Registers.R w)
    (aux : Stacks K) (a : Scalar c)
    (hw : (b+1)*control.wordFactor ≤ w)
    (he : ∀ i, input Z u z (decide (a=0)) i < 2^b) (hr : Registers.Stores rs Z u z) :
    let s := advance Z u z (decide (a=0))
    ∃ d ≤ checkClock w v e, ∃ rs',
      check.Runs d (scanBank n persistent rs [] (yielded aux (Engine.scalar v a)))
        (scanBank n persistent rs' [s.continues] (idle aux)) ∧
      Registers.Stores rs' Z (s.words 1) (s.words 2) := by
  let flag := decide (a=0)
  let s := advance Z u z flag
  have h₁ := zero_test hv n persistent rs aux a
  have h₂ : (SliceArithmetic.CallClear.clear (ScanPort.engine Engine.Port.result)).Runs (e*v+1)
      (scanBank n persistent rs [flag] (yielded aux (Engine.scalar v a)))
      (scanBank n persistent rs [flag] (idle aux)) := by
    have h := SliceArithmetic.CallClear.clear_runs (ScanPort.engine Engine.Port.result)
      (scanBank n persistent rs [flag] (yielded aux (Engine.scalar v a)))
    have heq : Function.update (scanBank n persistent rs [flag] (yielded aux (Engine.scalar v a)))
        (.engine .result) [] = scanBank n persistent rs [flag] (idle aux) := by
      funext k
      cases k with
      | engine j => cases j with | frame f => cases f <;> rfl | _ => rfl
      | _ => rfl
    rw [heq] at h
    exact (Engine.scalar_length v a) ▸ h
  obtain ⟨d, hd, out, hn, hs⟩ := Registers.next_runs Z u z flag persistent rs [] hw he hr
  have h₃ : (Registers.next.onPorts ScanPort.cursor).Runs d (scanBank n persistent rs [flag] (idle aux))
      (scanBank n persistent out [s.continues] (idle aux)) := by
    have ha : Registers.continuing s = s.continues := by cases s <;> rfl
    apply Registers.next.runs_onPorts_framed (ports := ScanPort.cursor) (fun _ _ h => ScanPort.cursor.inj h) hn
    · intro k; rfl
    · intro k; rw [← ha]; rfl
    · intro k hk; cases k with | cursor j => exact (hk j rfl).elim | _ => rfl
  exact ⟨(4*(e*v)+3) + (e*v+1) + d, by unfold checkClock; omega, out, (h₁.followedBy h₂).followedBy h₃, hs⟩

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
