import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepNative
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskNative

/-! # The fully assembled numeric spectral leaf -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Sweep

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROMAddress InterchangeAddress GeneratorSyntax
open InterchangeROMRepair.Physical (Allowance)
open InterchangeROMTable (numeral)

/-- All opcodes depending on a template use only its numeric data. -/
def nativeCommand (b n j p half : ℕ) (inv : Bool) : Cmd :=
  command (Physical.Mask.command b n j) b n j p half inv

def nativeRegs := regs Physical.Mask.within.choose

theorem native_within (b n j p half : ℕ) (inv : Bool) :
    Within nativeRegs (nativeCommand b n j p half inv) :=
  command_within (Physical.Mask.within.choose_spec b n j) b n j p half inv

theorem effective_native {X : Type} [Primcodable X] {b n j p half : X → ℕ} {inv : X → Bool}
    (hb : Computable b) (hn : Computable n) (hj : Computable j) (hp : Computable p)
    (hh : Computable half) (hi : Computable inv) :
    Effective ltr (fun x => nativeCommand (b x) (n x) (j x) (p x) (half x) (inv x)) :=
  effective_command (Physical.Mask.effective hb hn hj) hb hn hj hp hh hi

def maskTime (b n j : ℕ) (h : Header) (rows : ℕ) :=
  Physical.Mask.command_bounded.choose *
    (rows + (size (Physical.Mask.parameter b n j,h)+1)^Physical.Mask.command_bounded.choose_spec.choose + 1)

variable {I J D : Type} [DecidableEq J] {b n : ℕ}
  (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f l : I → ℕ) (payload : I → Series D)
  (j : J) (p half : ℕ) (inv : Bool)
  (x : (i : I) → domain (J:=J) (b:=b) P G B f i → D → ZMod (p+1)) (i : I)

def nativeCost (ac : Allowance) : Allowance :=
  let t := maskTime b n (ord j) (header (f i) (P i) (G i) (B i)) (countRows (b:=b) ord P G B f i)
  packedCost ord P G B f l payload j p half inv x i (uniformCost t) ac

/-- On any occupied lane bank the machine reshapes each coordinate using the actual recursive
callee. The requested field is one numeric instruction and never appears in an oracle. -/
theorem native_bounded (parent : Cmd) (env : Env) (ac : Allowance)
    (hb : 2 ≤ b) (hp : solid (P i)) (hg : solid (G i)) (hs : solid (B i))
    (hw : (payload i).count ≤ l i)
    (hc : let q := request ord P G B f l payload j p x i
      Run (parent::env) parent ((Request.job b).issue q) ((Request.job b).reply q) ac) :
    let rows := layoutRows (b:=b) ord P G B f i
    let h := send (header (f i) (P i) (G i) (B i))
    Run (parent::env) (nativeCommand b n (ord j) p half inv) (.fork h (row rows (payload i) (x i)))
      (row rows (payload i) fun k d =>
        InterchangeSpectralRequest.advance inv (half : ZMod (p+1)) j (fun k => x i k d) k)
      (nativeCost ord P G B f l payload j p half inv x i ac) := by
  apply packed_bounded ord P G B f l payload j p half inv x i _ parent env _ ac hw _ hc
  exact Physical.Mask.command_bounded.choose_spec.choose_spec ord j (P i) (G i) (B i)
    hb hp hg hs (f i) (parent::env)

end InterchangeROMRepair.Sweep

end

end NearSquareRoot
end Computability
end OAI
