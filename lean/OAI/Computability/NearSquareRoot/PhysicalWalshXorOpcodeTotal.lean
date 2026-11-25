import OAI.Computability.NearSquareRoot.PhysicalWalshXorOpcodeCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshXorRowTotal

/-! # Unconditional execution of a native Walsh XOR instruction

The header and collection commands use a workspace chosen for the actual
descriptor. The row scan uses the largest clock of the finitely many actual
prefix rows, including the unique row of a zero-bit prefix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow

open IntegerMultiplication Code Adic Strip Staff Loom Packed
open Controlled Controlled.PositionProgram XorReserve NamedPacked PositionRows

variable {X : Type} (r : Regime X) (P k : X → ℕ) (hP : Realizes r P)
    {U : X → Type} (u : (x:X) → Series (U x)) (op : X → Op) (f : (x:X) → Input (P x) (k x) (U x))

/-- A finite execution on each high-prefix row, with its actual payload and
the given input and output layouts. -/
def LocalRowsTotal (g : (x:X) → Input (P x) (k x) (U x)) (native : Cmd) : Prop :=
  let rr := fixedRowRegime r P hP
  ∃ t, EffectiveTask.Runs native t
    (fun z : (x:X) × Block 2 (P x) => Tree.fork (rr.header z)
      (stripe (line 2 (k z.1)) (fun b => strip (u z.1) (f z.1 (prefixBit b) z.2))))
    (fun z => stripe (line 2 (k z.1)) (fun b => strip (u z.1) (g z.1 (prefixBit b) z.2)))

theorem LocalRowsAt.total {g : (x:X) → Input (P x) (k x) (U x)}
    {l : X → ℕ} {speed : X → ℝ} {native : Cmd} (row : LocalRowsAt r P k hP u f g l speed native) :
    LocalRowsTotal r P k hP u f g native := by
  obtain ⟨_,_,carry⟩ := row
  obtain ⟨t,run,_⟩ := carry.work
  exact ⟨t,run⟩

set_option maxHeartbeats 800000 in
/-- The fixed disassembly and collection commands preserve the unrestricted
row execution. Workspace can depend on the actual descriptor and records. -/
theorem rowsOnNamedWithTotal {pre post native : Cmd} {e : ℕ} (g : (x:X) → Input (P x) (k x) (U x))
    (ends : RowEndsAt r P k hP u f pre post e g)
    (row : LocalRowsTotal r P k hP u f g native) :
    ∃ t s, EffectiveBoundedTask.Runs (opcodeCmd pre post native) t s
      (fun x => .fork (r.header x) (store (u x) (f x))) (fun x => store (u x) (g x)) := by
  classical
  let B x := payloadBits e (r.scale x)
  let m x := (u x).count+1
  have cellsFit (x:X) : (u x).count ≤ pack (B x) (m x) :=
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  obtain ⟨before,after⟩ := ends id B m r.scale cellsFit (fun _ => le_rfl) (fun _ => Nat.succ_pos _) (fun _ => le_rfl)
  let A x := Block 2 (P x)
  let cells x := line 2 (P x)
  let src x (a : A x) := Tree.fork ((fixedRowRegime r P hP).header ⟨x,a⟩)
    (stripe (line 2 (k x)) fun z => strip (u x) (f x (prefixBit z) a))
  let dst x (a : A x) := stripe (line 2 (k x)) fun z => strip (u x) (g x (prefixBit z) a)
  obtain ⟨time,run⟩ := row
  let clock (x : X) := Finset.univ.sup (fun a : A x => time ⟨x,a⟩)
  have cost (z : Sigma A) : time z ≤ clock z.1 := Finset.le_sup (f:=fun a => time ⟨z.1,a⟩) (Finset.mem_univ z.2)
  have priced := run.bound (b:=fun z => clock z.1 * 1) 1 (fun z => by simpa using cost z)
  let vol x := max ((stripe (cells x) (src x)).count) (max ((stripe (cells x) (dst x)).count) ((cells x).count*clock x))
  have scan := RowCommandScan.seriesRows native cells src dst clock vol (fun _ => 1) priced 1
    (fun _ => by simpa only [Nat.one_mul] using (le_max_left ..))
    (fun _ => by simpa only [Nat.one_mul] using (le_trans (le_max_left ..) (le_max_right ..)))
    (fun _ => (le_max_right ..).trans (le_max_right ..))
    (fun x => by change 1 ≤ (line 2 (P x)).count; rw [lineSize]; exact Nat.two_pow_pos _)
  exact ⟨_,_,AgendaOps.compose (AgendaOps.compose before scan) after⟩

set_option maxHeartbeats 800000 in
/-- The same frame and native row interpreter complete on every opcode input.
The workspace used in this existence proof may depend on the full input. -/
theorem opcodeTotal {pre post native : Cmd} {e : ℕ}
    (ends : RowEndsAt r P k hP u f pre post e (rewired P k op f))
    (row : NativeRowTotal r P k hP u native op f) :
    ∃ t s, EffectiveBoundedTask.Runs (opcodeCmd pre post native) t s
      (fun x => .fork (r.header x) (store (u x) (f x))) (fun x => store (u x) (rewired P k op f x)) := by
  apply rowsOnNamedWithTotal r P k hP u f (rewired P k op f) ends
  obtain ⟨t,run⟩ := row
  refine ⟨t,run.conform (fun _ => rfl) (fun _ => rfl) ?_⟩
  intro z
  change stripe _ (fun b => strip _ (f _ (prefixBit (nativeOp _ _ _ b)) _)) = _
  simp only [nativeOp_bits,rewired,Function.comp_apply]

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
