import OAI.ThreeFlat.RAM.SelfAdvice
import OAI.ThreeFlat.Diagonal.TraceBitPins

namespace OAI
/-! # One-bit trace of a native executable with a mounted instruction header -/

namespace ThreeFlat.Diagonal.NativeTrace
open Computability.VPVNP BurstRAM PrivateRAM RAMMemory RAM TraceBitHeader
variable {w p r k S base depth fuel : ℕ} {F : Type*} [Field F] [Fintype F]

/-- Only grid and scalar address inequalities for a concrete executable. -/
structure Fits (M : Machine w p r k) (S base depth fuel : ℕ) : Prop where
  width : 3≤w+1
  labels : p≤2^(w+1)
  positive : 0<p
  header : S≤2^w
  time : fuel≤2^(w+1)
  grid : S+fuel≤2^(1+depth)
  text : TextFits w p r k
  mount : base+(1+6*p+k)*w≤S

def executable (M : Machine w p r k) := RAM.installProgram M (fun _ : Fin ((1+6*p+k)*w) => false)

theorem executable_bits (M : Machine w p r k) : executable M = programBits M := by
  funext i
  simp [executable,installProgram,i.isLt]

/-- The virtual evaluator code in the trace is obtained from precisely the same description
that supplies the tick's instructions, its original D pin vector, and its separate advice. -/
theorem executable_from_description {p' r' k' q g : ℕ} (tick : Machine w p' r' k')
    (M : Machine w p r k) (extra : Fin g → Bool) (room : SelfAdvice.Fits w p' k' p k g q)
    (mount : ℕ) (raw : ℕ → Bool) :
    advicePins (S:=S) mount (SelfAdvice.hText room (SelfAdvice.description tick M extra)) raw =
      advicePins mount (executable M) raw := by
  rw [executable_bits]
  exact SelfAdvice.public_header tick M extra room mount raw

noncomputable def network (M : Machine w p r k) (fit : Fits M S base depth fuel)
    (hF : Fintype.card F≤2^w) (st : Word w) :=
  TraceBitHeader.network hF fit.width fit.labels base st fit.header fit.time r k depth

theorem installed (M : Machine w p r k) (fit : Fits M S base depth fuel)
    (hF : Fintype.card F≤2^w) (st : Word w) (pin : ℕ → Bool) :
    (network M fit hF st).eval (advicePins base (executable M) pin) =
      RAM.value (RAM.FieldCode.ofCardLe hF) M fuel st
        (memoryWithAdvice base (executable M) (initialMemory S (fun j => binaryWord w (pin j)))) := by
  rw [network,TraceBitHeader.eval_advice hF fit.width fit.labels fit.positive base st fit.header fit.time
    fit.grid (le_refl _) fit.mount]
  exact RAM.adviceValue_install _ M fit.text (le_refl _) _ _ _ _ _

end ThreeFlat.Diagonal.NativeTrace

end OAI
