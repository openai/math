import OAI.Hierarchy.DescentDatedPublicOrdinaryCode
import OAI.Hierarchy.DescentPublicReturnProgram

namespace OAI
/-! # Printed ordinary code after the scalar donor and before the private meter -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
@[ext] structure PrintedStep (w : ℕ) where
  program : Procedure w
  ticks : ℕ

namespace PrintedStep
def ofPhase {w : ℕ} (p : NativePhase w) : PrintedStep w:=⟨p.program,p.ticks⟩
def seq {w : ℕ} (x y : PrintedStep w) : PrintedStep w:=⟨x.program.seq y.program,x.ticks+y.ticks⟩
end PrintedStep

structure OrdinaryResultCode (w : ℕ) where
  signed : PrintedStep w
  argument : PrintedStep w
  funded : PrintedStep w
  returned : ReturnProgram
  primitive : PrintedStep w
  count : PrintedStep w

def OrdinaryResultCode.printed {w : ℕ} (r : OrdinaryResultCode w) : PrintedStep w :=
  ((((r.signed.seq r.argument).seq r.funded).seq
    ⟨r.returned.instructions w,r.returned.clock w⟩).seq r.primitive).seq r.count

namespace PhysicalOrdinary
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (root shelf header : ℕ)
    (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
    {w : ℕ} (s : ResultSteps w)
local notation "floor" => v.stageStart root
local notation "rank" => DescentOrdinaryVenueReturn.phase (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
  (v.materialEnd floor) v.k v.area.H v.area.D v.venue.hosts v.venue.degree w

def printedResult : OrdinaryResultCode w :=
  let first:=v.beforeSignedMaterial floor s.parts s.adjacency w
  let signs:=(((first.seq rank).seq (v.mark floor input w)).seq (v.signed.phase wires (v.markEnd floor) w))
  ⟨.ofPhase signs,.ofPhase s.arguments,.ofPhase s.paid,v.returnProgram floor B,
    .ofPhase s.primitive,.ofPhase (v.counter floor w)⟩

theorem finish_printed (safe : v.ResultRoom floor B w) :
    PrintedStep.ofPhase (v.finish floor input count wires B s safe)=
    (v.printedResult root input count wires B s).printed :=by
  rcases v.return_program_eq floor B w safe with ⟨one,two⟩
  apply PrintedStep.ext
  · dsimp only [finish,beforeCount,PrintedStep.ofPhase,OrdinaryResultCode.printed,printedResult,PrintedStep.seq,NativePhase.seq]
    rw [one]
  · dsimp only [finish,beforeCount,PrintedStep.ofPhase,OrdinaryResultCode.printed,printedResult,PrintedStep.seq,NativePhase.seq]
    rw [two]

/-- The matcher, scalar donor updates and final private count compile from the
public age. The measured successor exposes its printed blocks independently. -/
theorem date_printed (safe : v.ResultRoom floor B w) (dt : DonorDate) (positive : 0< dt.exponent) :
    let result:=(v.printedResult root input count wires B s).printed
    let load:=v.archivePhase root shelf w
    v.date root shelf header input count wires B s safe dt positive=
      dt.codeLoadedAfter v.gadget positive v.payload v.seats v.bitsPerField floor header w input
        ⟨v.prior.placement.wire,v.prior.placement.z,v.prior.placement.hist⟩
        load.program load.ticks result.program result.ticks :=by
  intro result load
  have phase:=v.finish_printed root input count wires B s safe
  have one:=congrArg PrintedStep.program phase
  have two:=congrArg PrintedStep.ticks phase
  change (v.finish floor input count wires B s safe).program=result.program at one
  change (v.finish floor input count wires B s safe).ticks=result.ticks at two
  unfold date
  rw [one,two]

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
