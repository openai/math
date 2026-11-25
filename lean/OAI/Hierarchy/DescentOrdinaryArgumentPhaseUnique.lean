import OAI.Hierarchy.DescentOrdinaryAfterSigned

namespace OAI
/-! # A single ordinary argument program for each numerical date chart -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentDatedPriorOperand DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentOrdinaryVenueIngress ProtocolRAM DescentOrdinaryReferenceInputs DescentPackedColony DescentOperandVectorArena
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

/-- A public description of storage, register widths and fixed operands. It contains
no field, graph, assignment, matching, or state reached by the descent. -/
@[ext] structure ArgumentPlan where
  clip : Clip
  venue : Inputs
  signedEnd : ℕ
  previous : DescentDatedPriorOperand.Layout
  previousBase : ℕ
  rolePitch : ℕ
  roleBits : ℕ
  role : Fin previous.blocks→Bank
  demand : ℕ
  reference : DescentOrdinaryRefsROM.Chart
  refsStart : ℕ
  born : DescentOrdinaryBorn.Chart
  vector : DescentOperandVectorArena.Layout
  resolver : DescentDatedPriorOperand.Layout
  origin : OriginPlan resolver
  grain : ℕ
  source : Fin resolver.jobs→Fin 8→Expr
  paths : clip.venue.paths=breadth reference.degree
  oldBlocks : previous.blocks=2^reference.k
  oldArgs : previous.operands≤vector.operands
  newBlocks : born.blocks=2^reference.k
  newCap : born.cap=reference.capacity
  newArgs : born.args=vector.operands

namespace ArgumentPlan
variable (p : ArgumentPlan)
def priorStart:=p.clip.fullEnd p.signedEnd
def roleStart:=DescentOrdinaryPriorPad.roof p.previous p.clip.venue.hosts p.clip.working p.priorStart
def roles : DescentOrdinaryRoleHostPad.Layout :=
  ⟨p.previous.blocks,p.previous.hosts,p.clip.venue.hosts,p.clip.venue.groups,p.rolePitch,p.clip.working,p.roleBits*p.reference.oldNodes⟩
def chipStart:=p.roles.roof p.roleStart
def chip : DescentOrdinaryBirthChip.Layout :=
  ⟨p.clip.venue.socket,p.clip.venue.hosts,p.clip.venue.groups,p.clip.working,p.clip.venue.profile,p.demand,p.clip.venue.slots⟩
def population : RoleControl.Layout :=
  ⟨p.chip.finish p.chipStart,p.clip.venue.hosts,p.clip.venue.groups,p.clip.working,p.clip.venue.paths,
   p.previous.blocks,p.reference.oldNodes,p.roleBits,p.reference.countBits,p.vector.lows⟩
def inlet (w : ℕ) : NativePhase w :=
  ((((p.clip.phase p.venue p.signedEnd w).seq
     (DescentOrdinaryPriorPad.phase p.previous p.clip.venue.hosts p.clip.working p.priorStart p.previousBase w)).seq
     (p.roles.phase p.roleStart p.role w)).seq (p.chip.phase p.chipStart (p.clip.clipped p.signedEnd p.venue).panel w)).seq
     (p.population.phase (p.clip.ports p.signedEnd) (p.roles.bank p.roleStart) w)
def refChart:=p.reference.withBase p.refsStart
def birthStart:=p.refsStart+p.reference.extent
def vectorStart:=p.born.endAddress p.birthStart
def routedStart:=p.vector.endAddress p.vectorStart
def directory : Directory p.refChart p.vector where
  previous:=p.previous
  tileBase:=p.priorStart
  priorHosts:=p.clip.venue.hosts
  priorPitch:=p.vector.lanes*p.vector.radix
  born:=p.born
  birthStart:=p.birthStart
  population:=p.population
  ports:=p.paths ▸ p.clip.ports p.signedEnd
  venues:=p.clip.fieldBank p.signedEnd
  prevBlocks:=p.oldBlocks
  prevSlots:=p.oldArgs
  birthBlocks:=p.newBlocks
  birthCap:=p.newCap
  birthArgs:=p.newArgs
  walks:=p.paths
  sites:=rfl

/-- The three observable components of a native phase, assembled from its public RAM descriptions. -/
structure Code (w : ℕ) where
  program : Procedure w
  ticks : ℕ
  image : Memory w→Memory w

def view {w : ℕ} (n : NativePhase w) : Code w:=⟨n.program,n.ticks,n.image⟩
def Code.seq {w : ℕ} (a b : Code w) : Code w:=⟨a.program.seq b.program,a.ticks+b.ticks,fun m=>b.image (a.image m)⟩
theorem view_injective {w : ℕ} : Function.Injective (@view w):=by
  rintro ⟨p,t,f,h⟩ ⟨q,u,g,j⟩ eqn
  change Code.mk p t f=Code.mk q u g at eqn
  cases eqn; rfl

def emit {w : ℕ} (prepare : Code w) : Code w:=
  let donor:=p.chip.bank p.chipStart
  let mnt : Code w:=⟨(p.refChart.program w).seq (p.born.program donor p.birthStart w),
    ((4+10*p.refChart.digitSize)+(4+10*p.refChart.tableSize))+p.born.ticks donor p.birthStart,
    fun m=>p.born.image donor p.birthStart (p.refChart.output m)⟩
  let choose : Cell (p.resolver.size+2):=p.grain
  let grain : Code w:=⟨DescentDatedPublicGrain.program p.resolver w (p.origin.grainBase p.routedStart) choose,
    DescentDatedPublicGrain.ticks p.resolver,DescentDatedPublicGrain.image p.resolver (p.origin.grainBase p.routedStart) choose⟩
  let outputs:=p.origin.outputs p.source p.routedStart
  let raster : Code w:=⟨program w outputs,clock outputs,result outputs⟩
  let ports:=fromVector p.resolver (p.vector.out p.vectorStart) (p.origin.side p.routedStart) (p.origin.route p.routedStart)
  let start:=p.routedStart+p.origin.routeWords
  let resolve : Code w:=⟨ports.program w start,ports.ticks start,ports.result start⟩
  (view (p.inlet w)).seq (mnt.seq (((((view (p.directory.refs.phase w p.vectorStart)).seq prepare).seq grain).seq raster).seq resolve))

end ArgumentPlan

variable {F P F' P' : Type} [Field F] [Field F']
def argumentPlan (v : PhysicalOrdinary F P) (floor : ℕ) (A : ArgumentEntry v) (match_ : A.Match v floor)
    (src : OriginSources v) : ArgumentPlan where
  clip:=A.clip;venue:=A.venue;signedEnd:=v.signedEnd floor
  previous:=A.previous;previousBase:=A.previousBase;rolePitch:=A.rolePitch;roleBits:=A.roleBits;role:=A.role
  demand:=v.gadget.b;reference:=v.reference;refsStart:=v.refsStart floor;born:=v.bornBook;vector:=v.vector
  resolver:=v.resolver;origin:=v.origin;grain:=DescentDatedPublicGrain.amount v.schedule v.gadget.b v.age;source:=src
  paths:=match_.paths;oldBlocks:=match_.oldBlocks;oldArgs:=match_.oldArgs
  newBlocks:=match_.newBlocks;newCap:=match_.newCap;newArgs:=match_.newArgs

set_option maxHeartbeats 1000000 in
theorem argumentPlan_emit {w : ℕ} (v : PhysicalOrdinary F P) (floor : ℕ) (A : ArgumentEntry v)
    (match_ : A.Match v floor) (src : OriginSources v) (prepare : NativePhase w)
    (early : (A.chipBank v floor).Fits w (v.refsStart floor)) (shape : v.VectorShape)
    (fit : v.endAddress floor<2^w) (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2) :
    (v.argumentPlan floor A match_ src).emit (ArgumentPlan.view prepare)=
    ArgumentPlan.view (v.argumentPhaseAfterSigned floor A match_ src prepare early shape fit wide):=rfl

theorem argumentPhaseAfterSigned_eq {w : ℕ} (v : PhysicalOrdinary F P) (u : PhysicalOrdinary F' P') (floor floor' : ℕ)
    (A : ArgumentEntry v) (B : ArgumentEntry u) (av : A.Match v floor) (bu : B.Match u floor')
    (x : OriginSources v) (y : OriginSources u) (prepare : NativePhase w)
    (ea : (A.chipBank v floor).Fits w (v.refsStart floor)) (eb : (B.chipBank u floor').Fits w (u.refsStart floor'))
    (sa : v.VectorShape) (sb : u.VectorShape) (fa : v.endAddress floor<2^w) (fb : u.endAddress floor'<2^w)
    (wa : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (wb : u.resolver.lanes*DescentPackedOperand.unit u.resolver.size≤w/2)
    (same : v.argumentPlan floor A av x=u.argumentPlan floor' B bu y) :
    v.argumentPhaseAfterSigned floor A av x prepare ea sa fa wa=u.argumentPhaseAfterSigned floor' B bu y prepare eb sb fb wb:=by
  apply ArgumentPlan.view_injective
  rw [←v.argumentPlan_emit,←u.argumentPlan_emit,same]

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
