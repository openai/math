import OAI.Hierarchy.DescentOrdinaryAfterSigned
import OAI.Hierarchy.DescentOrdinaryBornTariff

namespace OAI
/-! # The exact physical bill between the successor signed raster and the operand resolver -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentStaticWordColumn DescentDatedPriorOperand DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) {w : ℕ}

/-- We count the actual closed bytecode and its bounded clock at arbitrary linear prices. -/
def codeCharge (clockPrice textPrice ticks : ℕ) (q : Procedure w) :=
  clockPrice*ticks+textPrice*names q
def phaseCharge (clockPrice textPrice : ℕ) (p : NativePhase w) :=codeCharge clockPrice textPrice p.ticks p.program

private theorem price_seq (x y t u : ℕ) (p q : Procedure w) :
    codeCharge x y (t+u) (p.seq q)=codeCharge x y t p+codeCharge x y u q:=by
  simp only [codeCharge,names_seq,Nat.mul_add]
  omega
private theorem phase_seq (x y : ℕ) (p q : NativePhase w) :
    phaseCharge x y (p.seq q)=phaseCharge x y p+phaseCharge x y q:=price_seq ..

theorem argumentAfterSigned_bill (floor : ℕ) (A : ArgumentEntry v)
    (match_ : A.Match v floor) (src : OriginSources v) (prepare : NativePhase w)
    (donorFit : (A.chipBank v floor).Fits w (v.refsStart floor))
    (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (x y : ℕ) :
    let c:=phaseCharge (w:=w) x y
    c (v.argumentPhaseAfterSigned floor A match_ src prepare donorFit shape fit wide)=
      c (A.clip.phase A.venue (v.signedEnd floor) w)+
      c (DescentOrdinaryPriorPad.phase A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor) A.previousBase w)+
      c ((A.roleLayout v).phase (A.roleStart v floor) A.role w)+
      c ((A.chip v).phase (A.chipStart v floor) (A.chipSource v floor) w)+
      c ((A.population v floor).phase (A.ports v floor) (A.labels v floor) w)+
      codeCharge x y (v.refTime floor) ((v.refChart floor).program w)+
      codeCharge x y (v.bornBook.ticks (A.chipBank v floor) (v.birthStart floor))
        (v.bornBook.program (A.chipBank v floor) (v.birthStart floor) w)+
      c ((A.directory v floor match_).refs.phase w (v.vectorStart floor))+
      c prepare+c (v.grainPhase floor w)+c (v.rasterPhase floor src w)+c (v.resolvePhase floor w shape fit wide):=by
  dsimp only
  simp only [argumentPhaseAfterSigned,ArgumentEntry.inlet,resolvedPhase,routedArguments,phase_seq]
  have mounted : ∀(donor : Bank) (early : donor.Fits w (v.refsStart floor)) (cap : v.vectorStart floor<2^w),
      phaseCharge x y (v.mountPhase floor donor early cap)=
        codeCharge x y (v.refTime floor) ((v.refChart floor).program w)+
        codeCharge x y (v.bornBook.ticks donor (v.birthStart floor)) (v.bornBook.program donor (v.birthStart floor) w):=by
    intro donor early cap
    exact price_seq ..
  rw [mounted]
  omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
