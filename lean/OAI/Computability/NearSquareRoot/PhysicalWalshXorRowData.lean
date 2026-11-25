import OAI.Computability.NearSquareRoot.PhysicalWalshXorGate
import OAI.Computability.NearSquareRoot.NamedPackedRate

/-! # Actual prefix rows and local data of an elementary Walsh address instruction -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow
open IntegerMultiplication Code Adic Strip Staff Loom Packed
open Controlled Controlled.PositionProgram NamedPacked

variable {X : Type} (r : Regime X) (P k : X → ℕ) (hP : Realizes r P)
    {U : X → Type} (u : (x:X) → Series (U x))

noncomputable def beforeRows (f : (x:X) → Input (P x) (k x) (U x)) (x : X) : Tree :=
  stripe (line 2 (P x)) fun a => Tree.fork ((fixedRowRegime r P hP).header ⟨x,a⟩)
    (stripe (line 2 (k x)) fun b => strip (u x) (f x (prefixBit b) a))

noncomputable def afterRows (g : (x:X) → Input (P x) (k x) (U x)) (x : X) : Tree :=
  stripe (line 2 (P x)) fun a => stripe (line 2 (k x)) fun b => strip (u x) (g x (prefixBit b) a)

/-- The data transformation in the flat, unpartitioned window. -/
def rewired (op : X → Op) (f : (x:X) → Input (P x) (k x) (U x)) (x : X) : Input (P x) (k x) (U x) :=
  f x ∘ fun z => act (guardWidth (k x)) z (op x)

/-- The exact per-row cost contract requested from the native opcode dispatcher.
Each row sees the same global operation with its high spectator bits attached. -/
def NativeRowAt (c : Cmd) (ρ : ℝ) (op : X → Op) (f : (x:X) → Input (P x) (k x) (U x)) : Prop :=
  let rr := fixedRowRegime r P hP
  let bits (z : (x:X) × Block 2 (P x)) := k z.1
  let s z := line 2 (bits z)
  let payload (z : (x:X) × Block 2 (P x)) := u z.1
  let read (z : (x:X) × Block 2 (P x)) (b : Block 2 (bits z)) := f z.1 (prefixBit b) z.2
  BreezeAt c (Spindle.modes bits (τ:=ρ)) rr (fun z => (s z).count) (fun z => (payload z).count)
    (together rr.header (cloth s payload read)) (cloth s payload (fun z b =>
      read z (nativeOp (bits z) (guardWidth (bits z)) (op z.1) b)))

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
