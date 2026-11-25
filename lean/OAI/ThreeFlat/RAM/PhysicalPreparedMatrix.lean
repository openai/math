import OAI.ThreeFlat.RAM.PhysicalPreparedValue
import OAI.ThreeFlat.Diagonal.NetworkDiagonal

namespace OAI
/-! # The concrete H register-machine value is the approximating matrix entry -/

namespace ThreeFlat.RAM.PhysicalPinsInput

open Diagonal.BoundaryWire Diagonal.TraceCircuit

/-- Both external halves, in the same order as the paired binary header. -/
def externalBits {chunks a : ℕ} (x : Bool → Fin chunks → Fin a → Bool) :
    Fin (chunks*a+chunks*a) → Bool :=
  Fin.append (blocks chunks a (x false)) (blocks chunks a (x true))

theorem endpoint_externalBits {chunks a : ℕ} (x : Bool → Fin chunks → Fin a → Bool) :
    endpoint (externalBits x) = (x,fun _ => false) := by
  exact (stateEquiv chunks a).symm_apply_apply (x,fun _ => false)

end ThreeFlat.RAM.PhysicalPinsInput

namespace ThreeFlat.RAM.PhysicalPinsExpr.Program

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPrelude BitLayout Diagonal Diagonal.TraceAddressRecord Contraction
open scoped Fin.CommRing

attribute [local irreducible] program GeneratedContraction.machine FixedTraceProgram.program
  PhysicalPrelude.Image.procedure PhysicalProcedure.Procedure.link RAM.value
variable {F : Type*} [Fintype F] [Field F] {w q t shared b : ℕ}
variable (s : Shape) [NeZero s.period] (G : BitNetwork F q)
variable (input : Fin t → Fin q → BitSource shared (s.area+2*s.halfBits))
variable (keys : Fin q → Record) (params : Fin s.parameterBits → Bool)

set_option pp.explicit true in
theorem prepared_matrix_value (fit : Fits (H s (sourceNetwork s G input) params) w)
    (D : Fin s.advice → Bool) (x y : Bool → Fin s.chunks → Fin s.bits → Bool) (tail : Memory w)
    (space : (inputImage s G input keys params fit).Fits)
    (para : s.parameterBase=(inputImage s G input keys params fit).sizes.parameterBase)
    (templ : s.templateBase=(inputImage s G input keys params fit).sizes.templateBase)
    (margin : 5*b+128≤w) (shapeFit : ∀ p, s.words p<2^b)
    (rowsFit : (sourceNetwork s G input).cells≤2^b) (pinsFit : s.area+2*s.halfBits≤2^b)
    (blockFit : s.last+1≤2^b) (ticksFit : (s.last+1)*(s.inside+1)≤2^w)
    (teamFit : s.teams≤2^w) (eleven : 11≤2^b)
    (srcFit : 2+(s.area+2*s.halfBits)+(sourceNetwork s G input).internal<2^w)
    (widthFit : (sourceNetwork s G input).cells+s.halfBits<2^w)
    (state : Word w) (extra : ℕ) :
    RAM.value (codec (H s (sourceNetwork s G input) params) fit)
      (prepared s G input keys params fit)
      (extra+cost (w:=w) s (sourceNetwork s G input) params+preCost s G input keys params fit)
      state ((inputImage s G input keys params fit).tape D (PhysicalPinsInput.externalBits x) (PhysicalPinsInput.externalBits y) params tail) =
    Diagonal.approximatedMatrix (sourceNetwork s G input) D
      (fun i => ApproximateImage.select i.val params) (fun i => s.slots i.val) s.choice s.retained x y := by
  have h := prepared_tape_value s G input keys params fit D (PhysicalPinsInput.externalBits x)
    (PhysicalPinsInput.externalBits y) tail space para templ margin shapeFit rowsFit pinsFit blockFit
    ticksFit teamFit eleven srcFit widthFit state extra
  refine h.trans ?_
  rw [PhysicalPinsInput.endpoint_externalBits,PhysicalPinsInput.endpoint_externalBits]
  rfl


end ThreeFlat.RAM.PhysicalPinsExpr.Program

end OAI
