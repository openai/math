import OAI.ThreeFlat.RAM.PhysicalPreludeRun
import OAI.ThreeFlat.RAM.PhysicalPreparedMachine
import OAI.ThreeFlat.RAM.PhysicalRawTape
import OAI.ThreeFlat.RAM.PhysicalExternalOnly

namespace OAI
/-! # The H evaluator starting from the actual paired external memory -/

namespace ThreeFlat.RAM.PhysicalPinsExpr.Program

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPrelude BitLayout Diagonal Diagonal.TraceAddressRecord Contraction
open scoped Fin.CommRing

attribute [local irreducible] program GeneratedContraction.machine FixedTraceProgram.program
  PhysicalPrelude.Image.procedure PhysicalProcedure.Procedure.link RAM.value
variable {F : Type*} [Fintype F] [Field F] {w q t shared b : ℕ}
variable (s : Shape) [NeZero s.period] (G : BitNetwork F q)
variable (input : Fin t → Fin q → BitSource shared (s.area+2*s.halfBits))
variable (keys : Fin q → Record) (params : Fin s.parameterBits → Bool)

/-- From arbitrary external scratch and the short bit input, the linked RAM returns
the H value on the decoded catalyst halves and zero auxiliary registers. -/
theorem value_of_preparation (fit : Fits (H s (sourceNetwork s G input) params) w)
    (D : Fin s.advice → Bool) (x y : Fin (s.halfBits+s.halfBits) → Bool) (m : Memory w)
    (pre : Memory w → Prop) (preparationProc : PhysicalProcedure.Procedure w) (setup : ℕ) (initial : pre m)
    (cert : preparationProc.Spec pre (fun _ out => (inputImage s G input keys params fit).Ready D x y params out) setup)
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
      (preparationProc.link (native s (sourceNetwork s G input) params fit))
      (extra+cost (w:=w) s (sourceNetwork s G input) params+((4+(10+(program w).binds)+1)+setup))
      state m =
    (H s (sourceNetwork s G input) params).eval
      (BoundaryWire.pinBits D (PhysicalPinsInput.endpoint x) (PhysicalPinsInput.endpoint y)) := by
  let I := inputImage s G input keys params fit
  let X := sourceNetwork s G input
  let A := H s X params
  let baseTime := cost (w:=w) s X params
  let code := codec A fit
  obtain ⟨out,ready,rem,hrem,_,hr⟩ := PhysicalProcedure.Procedure.Spec.link_fixed cert (native s X params fit)
    (native_externalOnly s X params fit) code state m initial (extra+baseTime)
  let pins := PhysicalPinsInput.logical (a:=s.bits) D x y
  have pinEq := PhysicalPinsInput.logical_pins (a:=s.bits) (chunks:=s.chunks) D x y
  have stop : mulBase (sizePins s) A.internal A.cells ≤ I.sizes.parameterBase := by
    change mulBase _ _ _ ≤ mulBase _ _ _ + Fintype.card F*Fintype.card F
    exact Nat.le_add_right _ _
  have stop' : mulBase (sizePins s) A.internal A.cells ≤ I.sizes.templateBase :=
    stop.trans (Nat.le_add_right _ _)
  have paramReads (j : Fin s.parameterBits) : (out (s.parameterBase+j.val)).val=(params j).toNat := by
    rw [para]
    have bit : out (I.sizes.parameterBase+j.val) = bitWord w (params j) := ready.parameters j
    change (out (I.sizes.parameterBase+j.val)).val=(params j).toNat
    rw [bit]
    cases h : params j <;> simp [bitWord,Fin.ofNat,Nat.mod_eq_of_lt (show 1<2^w by
      exact Nat.one_lt_two_pow (by omega))]
  have image := value s X params fit pins out margin shapeFit rowsFit pinsFit blockFit ticksFit teamFit
    eleven srcFit widthFit (by rw [para]; exact stop) (by rw [templ]; exact stop') paramReads
    (fun i j => by rw [templ]; exact ready.template i j)
    (fun a ha away => away.elim (ready.low a) (fun h => ready.products a h ha))
    state (rem-baseTime)
  have sum : rem-baseTime+baseTime=rem := by omega
  change RAM.value code (native s X params fit) (rem-baseTime+baseTime) state out = A.eval pins at image
  rw [sum] at image
  rw [← pinEq]
  change RAM.value code (preparationProc.link (native s X params fit))
    ((extra+baseTime)+((4+(10+(program w).binds)+1)+setup)) state m = A.eval pins
  rw [← Nat.add_assoc (extra+baseTime) (4+(10+(program w).binds)+1) setup]
  exact hr.trans image

theorem prepared_value (fit : Fits (H s (sourceNetwork s G input) params) w)
    (D : Fin s.advice → Bool) (x y : Fin (s.halfBits+s.halfBits) → Bool) (m : Memory w)
    (initial : (inputImage s G input keys params fit).Raw D x y params m)
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
      state m =
    (H s (sourceNetwork s G input) params).eval
      (BoundaryWire.pinBits D (PhysicalPinsInput.endpoint x) (PhysicalPinsInput.endpoint y)) :=
  value_of_preparation s G input keys params fit D x y m _ _ _ initial
    ((inputImage s G input keys params fit).prepares D x y params space) para templ
    margin shapeFit rowsFit pinsFit blockFit ticksFit teamFit eleven srcFit widthFit state extra

/-- Evaluate a concrete paired bit tape with arbitrary existing external words after its end. -/
theorem prepared_tape_value (fit : Fits (H s (sourceNetwork s G input) params) w)
    (D : Fin s.advice → Bool) (x y : Fin (s.halfBits+s.halfBits) → Bool) (tail : Memory w)
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
      state ((inputImage s G input keys params fit).tape D x y params tail) =
    (H s (sourceNetwork s G input) params).eval
      (BoundaryWire.pinBits D (PhysicalPinsInput.endpoint x) (PhysicalPinsInput.endpoint y)) :=
  prepared_value s G input keys params fit D x y _
    ((inputImage s G input keys params fit).tape_raw D x y params tail) space para templ
    margin shapeFit rowsFit pinsFit blockFit ticksFit teamFit eleven srcFit widthFit state extra


end ThreeFlat.RAM.PhysicalPinsExpr.Program

end OAI
