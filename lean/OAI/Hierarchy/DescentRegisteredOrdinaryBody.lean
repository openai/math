import OAI.Hierarchy.DescentRegisteredReturnPorts
import OAI.Hierarchy.DescentRegisteredPrimitiveDevice
import OAI.Hierarchy.DescentOrdinaryBarePlan
import OAI.Hierarchy.DescentIssuedOrdinaryResult

namespace OAI
/-! # The six parts of the ordinary successor on its registered public layout -/
namespace Hierarchy.DescentSixParty.Chronology
open PhysicalOrdinary DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentOrdinaryVenueIngress DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
namespace VenueProgram.Registered
variable {F : Type} [Field F] (G : PoweredGadget F) (r : VenueProgram.Registered)
  (p : ArgumentPlan) (stage : ℕ) (prior : DatePorts) (w : ℕ)

structure BodyFits : Prop where
  signed : r.core.prefixProgram.Chart
  selector : p.SelectorShape r.core
  slots : 0<p.vector.operands

def body (h : r.BodyFits p) : OrdinaryResultCode w :=
  let page : Fin (7*p.vector.operands):=⟨0,Nat.mul_pos (by decide) h.slots⟩
  let prep:=p.ticketPreparation r.core h.selector h.signed w page
  let bound:ArgumentPlan:={p with source:=p.selectorPort r.core h.selector}
  let code:=bound.emit (ArgumentPlan.view prep)
  let ranked:DescentOrdinaryVenueReturn.Sources:=⟨prior.archive.count,prior.io.roster,prior.io.hubs⟩
  let padded:=r.core.prefixProgram.four h.signed w p.venue.panel p.venue.adjacency ranked prior.io
  let address:=VenueProgram.operandEnd r.chart r.core.donorEnd r.installed
  let primitive:=p.paletteDevice G r.installed.palette r.clip.working address
  let a:=r.core.area
  let scan:=DescentOrdinaryCountScan.program w (a.matcher prior.io.roster stage).layout.topology
    (DescentPacking.PackedMatch.chunkCount a.shapeAt a.lanesAt) (VenueProgram.primitiveEnd G r.chart r.core.donorEnd r.installed) a.batch
  ⟨.ofPhase padded,⟨code.program,code.ticks⟩,r.fundedCode prior.io w,
    VenueProgram.returned r.chart r.core.donorEnd r.installed.metadata,.ofPhase (primitive.phase w),
    ⟨scan,DescentOrdinaryCountScan.clock (a.shapeAt.outputBits*a.lanesAt) a.batch⟩⟩

theorem body_congr {r' : VenueProgram.Registered} {p' : ArgumentPlan} (regs : r=r') (plan : p=p')
    (h : r.BodyFits p) (h' : r'.BodyFits p') :
    body G r p stage prior w h=body G r' p' stage prior w h' :=by
  subst r'
  subst p'
  rfl
end VenueProgram.Registered

namespace PhysicalOrdinary
variable {F P : Type} [Field F] (b : PhysicalOrdinary F P) (origin : ℕ) (prior : DatePorts) (w : ℕ)
set_option hygiene false
local notation "stage" => b.stageStart origin
local notation "v" => b.registeredFrom prior stage
local notation "entry" => b.registeredEntry prior stage
variable (cap : prior.argumentsPerNode≤b.vector.operands)
local notation "m₀" => b.registered_match prior stage cap
local notation "sh" => b.registered_geometry prior stage
local notation "p₀" => (v).bareArguments stage entry m₀
variable (cs : (v).SignedChart) (blocks : (v).resolver.blocks=(v).material.blocks)
    (paths : (entry).clip.venue.paths=StageVenueTail.OrdinaryRaster.paths (v).area)
    (slots : 0<(v).vector.operands)
local notation "regs" => (v).returnRegisters stage entry paths

set_option hygiene true

include cs blocks paths slots in
theorem registered_body_fits : (regs).BodyFits p₀ :=
  by exact ⟨(v).publicSignedChart stage cs,(v).selectorShape stage entry m₀ sh blocks,slots⟩


private theorem resultCode_eq {w : ℕ} (left right : OrdinaryResultCode w)
    (s : left.signed = right.signed) (a : left.argument = right.argument)
    (f : left.funded = right.funded) (r : left.returned = right.returned)
    (p : left.primitive = right.primitive) (c : left.count = right.count) : left = right := by
  cases left
  cases right
  cases s
  cases a
  cases f
  cases r
  cases p
  cases c
  rfl

attribute [local irreducible] ArgumentPlan.emit SignedProgram.four FundedProgram.fromChart
  DescentOrdinaryCountScan.program VenueProgram.returned PrimitiveDevice.phase

include cs blocks paths slots in
theorem registered_body (old : b.old=prior.io.roster) :
    (v).issuedResult origin prior entry cs w m₀ sh blocks paths slots =
      (regs).body b.gadget p₀ stage prior w (b.registered_body_fits origin prior cap cs blocks paths slots) :=by
  apply resultCode_eq
  · rfl
  · have src : (p₀).selectorPort ((v).staticCore stage) ((v).selectorShape stage entry m₀ sh blocks) =
        (v).nativeTicketExpr stage cs entry m₀ sh blocks :=
      funext fun j => funext fun f => (v).ticket_expression_plan stage entry m₀ sh blocks cs j f
    have prep := (v).ticket_preparation_plan stage entry m₀ sh blocks cs w
      (⟨0,Nat.mul_pos (by decide : 0<7) slots⟩ : Fin (7*(v).vector.operands))
    let printed (sources : OriginSources (v)) (before : NativePhase w) : PrintedStep w :=
      let out := ((v).argumentPlan stage entry m₀ sources).emit (ArgumentPlan.view before)
      ⟨out.program,out.ticks⟩
    exact congrArg₂ printed src.symm prep.symm
  · rfl
  · exact ((v).return_from_chart stage).trans (congrArg
      (fun chart => VenueProgram.returned chart ((v).donorEnd stage) (v).metadata)
      ((v).registered_return_chart stage entry rfl))
  · rfl
  · dsimp only [issuedResult,resultCode,VenueProgram.Registered.body]
    rw [←old]
    rfl

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
