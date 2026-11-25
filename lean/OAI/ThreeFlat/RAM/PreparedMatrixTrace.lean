import OAI.ThreeFlat.RAM.PhysicalPreparedMatrix
import OAI.ThreeFlat.Diagonal.TracePreparedTape
import OAI.ThreeFlat.Diagonal.NativeTrace

namespace OAI
/-! # Open paired trace of the real H evaluator has exactly its approximating-matrix coefficient -/

namespace ThreeFlat.RAM.PhysicalPinsExpr.Program

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPrelude BitLayout Diagonal Diagonal.TraceAddressRecord Contraction
open scoped Fin.CommRing
attribute [local irreducible] program GeneratedContraction.machine FixedTraceProgram.program
  PhysicalPrelude.Image.procedure PhysicalProcedure.Procedure.link RAM.value
variable {F : Type*} [Fintype F] [Field F] {w q t shared b : ℕ}
variable (s : Shape) [NeZero s.period] (G : BitNetwork F q)
variable (input : Fin t → Fin q → BitSource shared (s.area+2*s.halfBits))
variable (keys : Fin q → Record) (params : Fin s.parameterBits → Bool)

theorem trace_matrix_entry (fit : Fits (H s (sourceNetwork s G input) params) w)
    (D : Fin s.advice → Bool) (x y : Bool → Fin s.chunks → Fin s.bits → Bool)
    (space : (inputImage s G input keys params fit).Fits)
    (para : s.parameterBase=(inputImage s G input keys params fit).sizes.parameterBase)
    (templ : s.templateBase=(inputImage s G input keys params fit).sizes.templateBase)
    (margin : 5*b+128≤w) (shapeFit : ∀ p, s.words p<2^b)
    (rowsFit : (sourceNetwork s G input).cells≤2^b) (pinsFit : s.area+2*s.halfBits≤2^b)
    (blockFit : s.last+1≤2^b) (ticksFit : (s.last+1)*(s.inside+1)≤2^w)
    (teamFit : s.teams≤2^w) (eleven : 11≤2^b)
    (srcFit : 2+(s.area+2*s.halfBits)+(sourceNetwork s G input).internal<2^w)
    (widthFit : (sourceNetwork s G input).cells+s.halfBits<2^w)
    (state : Word w) (extra : ℕ) {S base depth : ℕ}
    (target : NativeTrace.Fits (prepared s G input keys params fit) S base depth
      (extra+cost (w:=w) s (sourceNetwork s G input) params+preCost s G input keys params fit))
    (rawFits : (inputImage s G input keys params fit).sizes.rawCount≤base) :
    let I := inputImage s G input keys params fit
    let M := prepared s G input keys params fit
    let px := PhysicalPinsInput.externalBits x
    let py := PhysicalPinsInput.externalBits y
    (NativeTrace.network M target (card_le_word _ fit) state).eval
        (TraceBitHeader.advicePins base (NativeTrace.executable M) (I.tapeBit D px py params)) =
      Diagonal.approximatedMatrix (sourceNetwork s G input) D
        (fun i => ApproximateImage.select i.val params) (fun i => s.slots i.val) s.choice s.retained x y := by
  dsimp only
  rw [NativeTrace.installed]
  have enough : (inputImage s G input keys params fit).sizes.rawCount≤S := by have := target.mount; omega
  have raw := TraceBitHeader.prepare_raw (inputImage s G input keys params fit) enough rawFits
    (NativeTrace.executable (prepared s G input keys params fit)) D (PhysicalPinsInput.externalBits x)
    (PhysicalPinsInput.externalBits y) params
  have h := prepared_value s G input keys params fit D (PhysicalPinsInput.externalBits x)
    (PhysicalPinsInput.externalBits y) _ raw space para templ margin shapeFit rowsFit pinsFit blockFit
    ticksFit teamFit eleven srcFit widthFit state extra
  refine h.trans ?_
  rw [PhysicalPinsInput.endpoint_externalBits, PhysicalPinsInput.endpoint_externalBits]
  rfl

end ThreeFlat.RAM.PhysicalPinsExpr.Program

end OAI
