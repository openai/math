import OAI.Hierarchy.DescentDatedPrimitiveCode
import OAI.Hierarchy.DescentOrdinaryArgumentPhaseUnique
import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentDatedOrdinaryCountRoof

namespace OAI
/-! The issued primitive update and its returned banks depend on the numeric operand plan. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint DescentPrimitivePalette DescentOrdinaryOriginMask
open ProtocolRAM DescentKernelHistory
noncomputable section
variable {F P Q : Type} [Field F]

namespace ArgumentPlan
variable (p : ArgumentPlan)
def paletteReceipt : DescentOrdinaryOriginMask.Return :=
  ⟨p.reference.degree,p.reference.k,p.reference.oldNodes,p.reference.capacity,p.resolver.nodes,
    Nat.clog 2 (p.reference.nodes+1),p.vector.hosts,p.vector.lows,p.vector.groups,p.vector.radix,p.vector.lanes⟩

def paletteDevice (G : PoweredGadget F) (config : DescentOrdinaryPalette.Configuration) (storedPitch start : ℕ) :
    PrimitiveDevice F where
  gadget:=G
  config:=config
  shape:=⟨p.vector.hosts,p.reference.degree,p.reference.k,p.reference.capacity,p.vector.lows,p.vector.groups,
    p.reference.oldNodes,p.resolver.nodes,printedBits G config.seedWidth config.grainLimit config.rotor,
    Nat.clog 2 (p.reference.nodes+1),storedPitch,p.born.lanes,p.vector.lanes,config.workLanes,config.nextLanes⟩
  births:=p.born
  floor:=start
  chip:=p.chip.bank p.chipStart
  past n:=if h:n<p.previous.blocks then p.roles.bank p.roleStart ⟨n,h⟩ else ⟨0,0⟩
  origins n:=if h:n<p.vector.radix then p.paletteReceipt.returned p.routedStart ⟨n,h⟩ else ⟨0,0⟩
  halo:=(p.clip.ports p.signedEnd).roster
end ArgumentPlan

variable (v : PhysicalOrdinary F P) (u : PhysicalOrdinary F Q) (floor base : ℕ)
variable (A : ArgumentEntry v) (B : ArgumentEntry u) (av : A.Match v floor) (bu : B.Match u base)
variable (src : OriginSources v) (dst : OriginSources u)
theorem primitive_from_plan :
    v.primitiveDevice floor A=(v.argumentPlan floor A av src).paletteDevice v.gadget v.palette
      v.rasterLanes (v.operandEnd floor):=rfl

/-- For two issued dates, compare just the common operand plan and public register parameters. -/
theorem primitive_device_public
    (plans : v.argumentPlan floor A av src=u.argumentPlan base B bu dst)
    (gadget : v.gadget=u.gadget) (palette : v.palette=u.palette)
    (pitch : v.rasterLanes=u.rasterLanes) (start : v.operandEnd floor=u.operandEnd base) :
    v.primitiveDevice floor A=u.primitiveDevice base B:=by
  rw [primitive_from_plan v floor A av src,primitive_from_plan u base B bu dst,plans,gadget,palette,pitch,start]

theorem registered_primitive_device_public (ports : DatePorts) (av₀ : ports.argumentsPerNode≤v.vector.operands)
    (bu₀ : ports.argumentsPerNode≤u.vector.operands)
    (src₀ : OriginSources (v.registeredFrom ports floor)) (dst₀ : OriginSources (u.registeredFrom ports base))
    (plans : (v.registeredFrom ports floor).argumentPlan floor (v.registeredEntry ports floor) (v.registered_match ports floor av₀) src₀ =
      (u.registeredFrom ports base).argumentPlan base (u.registeredEntry ports base) (u.registered_match ports base bu₀) dst₀)
    (gadget : v.gadget=u.gadget) (palette : v.palette=u.palette)
    (start : (v.registeredFrom ports floor).operandEnd floor=(u.registeredFrom ports base).operandEnd base) :
    (v.registeredFrom ports floor).primitiveDevice floor (v.registeredEntry ports floor)=
      (u.registeredFrom ports base).primitiveDevice base (u.registeredEntry ports base):=by
  apply primitive_device_public _ _ _ _ _ _ _ _ _ _ plans gadget palette _ start
  exact congrArg (fun p:ArgumentPlan=>p.clip.working) plans

private theorem primitive_bank_eq {d e : PrimitiveDevice F} (same : d=e) (x : Fin d.shape.blocks) :
    d.shape.bank (DescentOrdinaryPaletteBirth.roof d.births d.floor) x =
      e.shape.bank (DescentOrdinaryPaletteBirth.roof e.births e.floor)
        (x.cast (congrArg (fun dev : PrimitiveDevice F => dev.shape.blocks) same)) := by
  cases same
  rfl

/-- The same device prints the same concrete code and keeps the same immutable addresses. -/
theorem public_primitive_outputs (same : v.primitiveDevice floor A=u.primitiveDevice base B)
    (r : v.vector.radix=2^v.reference.k) (r' : u.vector.radix=2^u.reference.k) (w : ℕ) :
    v.primitiveUpdate floor A av r w=u.primitiveUpdate base B bu r' w ∧
    v.primitiveEnd floor=u.primitiveEnd base ∧
    ∃arity : 2^v.reference.k=2^u.reference.k,∀x,
      v.primitiveBank (v.operandEnd floor) x=u.primitiveBank (u.operandEnd base) (x.cast arity):=by
  refine ⟨(primitive_device v floor A av r w).trans ((congrArg (fun d:PrimitiveDevice F=>d.phase w) same).trans
    (primitive_device u base B bu r' w).symm),?_,?_⟩
  · have roof := congrArg (fun d : PrimitiveDevice F =>
      d.shape.roof (DescentOrdinaryPaletteBirth.roof d.births d.floor)) same
    simpa only [primitiveDevice, primitiveEnd, primitiveRoof, primitiveFirst] using roof
  · let arity := congrArg (fun d : PrimitiveDevice F => d.shape.blocks) same
    refine ⟨arity, fun x => ?_⟩
    have banks := primitive_bank_eq same x
    dsimp only [primitiveDevice] at banks
    dsimp only [primitiveBank, primitiveFirst]
    refine banks.trans (congrArg (u.paletteShape.bank _) ?_)
    exact Fin.ext rfl

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
