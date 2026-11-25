import OAI.Hierarchy.GridNativeDistribution

namespace OAI
/-! # Distribution on the originally selected machine, address chart and clock -/

noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1100000
namespace Hierarchy.GridThrough
open ThreeFlat RAM Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory
open UniversalGrid TraceDistribution
open scoped Classical BigOperators

attribute [local irreducible] Physical.run GridNativeEvaluator.machine
  ThreeFlat.Diagonal.TraceStaticRow.gateTable

variable {F : Type} [Field F] [Fintype F]
variable {k q p n e a cap W tp tr tk up ur uk size start budget axes low : ℕ}
/-- Transport the native grid equality at the program boundary. The actual
physical compression, its table and all scheduled settings retain their
original dependent types until both self-installation equations are used. -/
def mounted_distribution
    (N : BitNetwork F p) (X : Catalyst.Approximation F k (q*p)) (dir : Fin e→Fin k)
    (recv : Machine W tp tr tk) (sends : PhysicalProcedure.Procedure W) (hf : Fintype.card F≤2^W)
    (hp : (9+sends.labels)+35≤up) (hr : sends.registers+10≤ur) (hs : sends.slots+5≤uk)
    {actualBase actualFuel : ℕ} (E : Machine W up ur uk) :
    let padded := CapacityPadding.pad
      (GridNativeEvaluator.machine sends start (cap+1)
        (GridNativeEvaluator.parameters (e:=e) (n:=n) X hf)) hp hr hs
    let bytes := GridDescription.code (q:=a) recv E
    let mount := e*2+SelfAdvice.textSize W tp tk
    let finishTime := GridNativeEvaluator.tailTime (e:=e) (n:=n) X
    ∀ (extra : ℕ) (fit : NativeTrace.Fits E size actualBase ((axes+1)+low) actualFuel) (st : Word W)
      (B : Block F) (axesFit : 2≤axes+1) (passes : ℕ) (axesRoom : B.blockCharge*passes≤axes+1),
    let run := Physical.nativeRun B axesFit E fit hf st passes axesRoom
    let grades := fun h : run.plan.History => GridPhysicalSelector.bits run h
    let siteOrder := GridPhysicalSelector.siteOrder run
    let wires := run.terminalLabels
    let selectedTrace := GridSelector.Trace run.plan grades
    ∀ (C : run.plan.Codes) (fixed : ℕ→Bool),
    let tape := fun x : GridDiagonal.Pins (Fin e) =>
      GridDescription.input (x ∘ Wiring.railPin.symm) bytes fixed
    let seed := fun x : GridDiagonal.Pins (Fin e) =>
      Physical.seed B axesFit (TraceDistribution.layout E fit hf st) (fun i => tape x i.val)
    ∀ (setting : Option selectedTrace → Setting X n e dir),
    let control : Bits a → Bits (cap+1) → Option (Setting X n e dir) :=
      honestController run.plan C grades setting bytes
    let G := grid N X dir control
    ∀ (_installation : E=padded) (_location : actualBase=mount)
    (_duration : actualFuel=((extra+finishTime+budget)+4+5*(cap+1)))
    (_memory : GridNativeEvaluator.footprint (n:=n) (e:=e) X≤2^W)
    (_address : start+(cap+1)<2^W) (_codeRoom : SelfAdvice.Fits W tp tk up uk 0 a)
    (_selectorRoom : GridSelector.Room run.plan C grades cap)
    (_noTouch : ∀ j,(setting none).1.touch j=none)
    (_unit : ∀ c,Catalyst.tickProduct N q ((setting none).1.dataBits (fun _=>false) c)=1)
    (_allTouch : ∀ z j,(setting (some z)).1.touch j≠none) (_npos : 0<q)
    (exponent : ℕ) {dims : ℕ}
    (cost : (z : selectedTrace) → Fin (Fintype.card (run.plan.finish z.1).Site) → Fin dims → ℕ)
    (_write : ∀ (x : GridDiagonal.Pins (Fin e)) (s : Bits (cap+1)),
      TickStageSpec.Admission (FieldCode.ofCardLe hf) sends.block sends.publicData
        (·=GuessLoop.install start s (initialMemory size (fun j => TraceBitHeader.binaryWord W (tape x j))))
        (fun _ => (control bytes s).isSome) (fun _ out => ∀ v : Setting X n e dir, control bytes s=some v →
          ∀ i<BitLayout.footprint (GridNativeEvaluator.net X v.1), out i =
            BitLayout.memory (GridNativeEvaluator.net X v.1) (FieldCode.ofCardLe hf)
              (x ∘ Wiring.railPin.symm) (fun _=>false) i) budget)
    (_receive : ∀ (z : selectedTrace) (x : GridDiagonal.Pins (Fin e)) c j,
      N.eval (fun i => (setting (some z)).1.dataBits x c (finProdFinEquiv (j,i))) =
        ((FactorAllocation.factors exponent (cost z) (List.ofFn id) (GridTicks.index (c,j))).map
          (fun i => cellFactor run.plan grades siteOrder wires seed z i x)).prod),
    G.Distributed bytes := by
  intro padded bytes mount finishTime extra fit st B axesFit passes axesRoom run grades siteOrder wires
    selectedTrace C fixed tape seed setting control G installation location duration memory address codeRoom selectorRoom
    noTouch unit allTouch npos exponent dims cost write receive
  subst E
  subst actualBase
  subst actualFuel
  exact native_distribution N X dir recv sends hf hp hr hs extra fit st B axesFit passes
    axesRoom C fixed setting memory address codeRoom selectorRoom noTouch unit allTouch npos
    exponent cost write receive

end Hierarchy.GridThrough
end

end OAI
