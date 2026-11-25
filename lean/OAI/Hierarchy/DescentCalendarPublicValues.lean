import OAI.Hierarchy.DescentCalendarPublicOperandControls
import OAI.Hierarchy.DescentDatedPublicValues

namespace OAI
/-! All public decoder values at the registered reset, indexed by its original measured inverse and charged packet rows. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentDenseHostOrder DescentActorRaster
open DescentPackedZip DescentSIMDLookup DescentPackedColony DescentDatedAddressBook DescentResetControlRegisters
open DescentVenueQuantityPlanes
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {old : Reached W G q ε S k i z D wire hist} {rates : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset old rates) {oldH H oldM M w : ℕ}
    (previous : Fintype.card old.V ≤ oldH) (next : Fintype.card B.next.V ≤ H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "Q" => (DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) (GroupStage.depthBound D n f g)).card
local notation "J" => S.groupCount (i+1)
local notation "cap" => old.placement.cap
local notation "oldId" => old.vertex.trans (Fin.castLEEmb previous)
local notation "rank" => (B.frame.host.symm.toEmbedding.trans old.vertex).trans (Fin.castLEEmb previous)
local notation "shapeId" v => ((Z).hostFields T rank v).2.val
local notation "depthAt" v => (Z).placement.b (position (Z).graph (v).val)
local notation "dims" => quantityDims B 1 oldH H oldM M
local notation "values" x => fun host group=>actualBit B next host group x
variable {A : PhysicalReset} {floor : ℕ} (u : A.DateInputs floor w) (ok : u.Ready)
local notation "V₀" => A.successor
local notation "base₀" => A.rebased floor
local notation "U₀" => (V₀).actor
local notation "cb" => (V₀).middle.stop base₀
local notation "first" => (U₀).endAddress cb
local notation "dir" => (⟨first,oldH,Q,chunks (2^cc) oldM⟩ : DescentResetNewActorDirectory.Layout)
local notation "scene" => (U₀).scene cb
local notation "depths" => (U₀).depths cb
local notation "levels" => (U₀).levels cb
local notation "a₀" => (V₀).setup.rotorBits
local notation "c₀" => (⟨dims,a₀⟩ : Chart)
local notation "start" => (V₀).controlFloor base₀
local notation "ceiling" => (V₀).operandFloor base₀
local notation "head₀" => A.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "time₀" => A.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "op₀" => (U₀).actorBody u.actor cb w
local notation "clock₀" => (U₀).actorTicks u.actor cb w


open DescentDatedAddressBook.PhysicalReset.DateInputs
local notation "C₀" => (V₀).setup
local notation "S₀" => (V₀).sheets
local notation "coord" => (S₀).stemSources.coord
local notation "nativeH" => (C₀).placement.newHosts
local notation "nativeG" => (C₀).placement.groups
local notation "basisBase" => (S₀).metaEnd ((V₀).remap base₀).endAddress
local notation "basisEnd" => (S₀).coordinateEnd ((V₀).remap base₀).endAddress

private theorem secondary_cast {h h' n n' : ℕ} (h₁ : h=h') (h₂ : n=n') (r : Fin (h*n)) :
    (finProdFinEquiv.symm (r.cast (congrArg₂ Nat.mul h₁ h₂)) : Fin h'×Fin n').2.val =
    (finProdFinEquiv.symm r : Fin h×Fin n).2.val :=by
  subst h';subst n';rfl

variable (x : DescentColonies.Block k) (blockCount : 2^k=A.successor.setup.placement.blocks)
local notation "x₀" => x.cast blockCount
local notation "live_" => (V₀).controlRegisters.live start x.val
local notation "reg_" => (V₀).controlRegisters.ports start (A.c/2) x.val ((U₀).directory cb).inverse depths levels
private abbrev publicBlockPorts := PhysicalReset.OperandMenu.publicPorts (a:=A) u.shape floor u.count u.hub u.g u.Y live_ reg_
local notation "P₀" => publicBlockPorts u x
variable (hostFit : A.successor.setup.placement.newHosts=H)
  (groupFit : A.successor.setup.placement.groups=S.groupCount (i+1))
  (controlBits : A.successor.setup.rotorBits=(publicBlockPorts u x).casts.bits)
variable (controlPitch : M=(publicBlockPorts u x).casts.lanes) (capAt : A.c/2=old.placement.cap)
variable (hRaw : oldH=A.successor.setup.placement.oldHosts)
  (sRaw : (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth)
    (GroupStage.depthBound D n f g)).card=A.successor.setup.placement.shapes)
local notation "numeric" => (fun j=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hRaw sRaw))
local notation "left_" => resetRowCast hostFit groupFit controlBits ((c₀).enabled (values x) (fun _=>1))
local notation "right_" => (fun j : Fin 4=>resetRowCast hostFit groupFit controlBits ((c₀).enabled (values x)
   (controlScalar B previous next j)))
variable {N : ℕ} (R : u.MeasuredChannels N)
  (basis : DescentGL.Layout A.successor.sheets.stemSources.coord.dim)
variable (ah : A.successor.setup.placement.newHosts=A.successor.sheets.hosts)
  (ag : A.successor.setup.placement.groups=A.successor.sheets.groups)
  (aw : A.successor.sheets.metaBits=(publicBlockPorts u x).casts.width 2)
variable (ch : A.successor.setup.placement.newHosts=A.successor.sheets.stemSources.coord.hosts)
  (cg : A.successor.setup.placement.groups=A.successor.sheets.stemSources.coord.groups)
  (cw : A.successor.sheets.stemSources.coord.width=(publicBlockPorts u x).casts.width 1)
variable (digits : (publicBlockPorts u x).casts.bits=A.successor.setup.fallbackBits)
variable (packet : (f : Bool)→Fin ((publicBlockPorts u x).packets.stage 0 f).fields→
  Fin (publicBlockPorts u x).packets.blocks→Fin A.successor.setup.placement.newHosts→
    Fin A.successor.setup.placement.groups→Cell ((publicBlockPorts u x).casts.width 0))
local notation "issued" => u.issuedPublicValues x₀ R basis ah ag aw ch cg cw left_ right_ packet

attribute [local irreducible] DescentPackedZip.Source

set_option maxHeartbeats 500000 in
include capAt controlPitch in
theorem public_values_at_date (grid : (U₀).directory cb=dir)
    (chart : (V₀).controlRegisters=c₀)
    (m before : Memory w)
    (ran : ((head₀).seq op₀).Exec m ((dir).result scene before) (time₀+clock₀))
    (cheap : CheapCode ((head₀).seq op₀))
    (oldPos : 0 < oldM) (newPos : 0 < M) (oldBits : oldM ≤ w)
    (actors : ∀(j : Fin Q) (p : Row oldH (2^cc) oldM),
      before ((scene).base+j.val*(oldH*chunks (2^cc) oldM)+(row _ _ _ p).val)=
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) j) p).val:Word w))
    (oldDepth : ∀v,before ((depths).base+(oldId v).val)=((Z).placement.b (B.frame.host v):Word w))
    (oldLevels : ∀j,j < (levels).size → before ((levels).base+j)=((j-cc+1:ℕ):Word w))
    (depthWidth : ∀v : B.next.V,(depthAt v) ≤ (U₀).oldWidth)
    (short : ∀v : B.next.V,∀t∈[1,cap,(depthAt v)-cc+1,shapeId v],t < 2^a₀)
    (captured : PhysicalReset.DateInputs.CaptureRoom R ((dir).result scene before))
    (saved : u.originalBasis.Fits w basisBase) (room : basisEnd<2^w)
    (chosen : u.masked.image (u.privateResult ((dir).result scene before)) u.originalBasis.base=
      ((DescentExterior.matrixCode basis).val:Word w))
    (auxPitch : (S₀).lanes=(P₀).casts.lanes) (coordPitch : (coord).lanes=(P₀).casts.lanes)
    (packetRead : ∀f j z,let t:=(P₀).packets.src (P₀).packetBase f j z
      t.Fits w (P₀).castBase ∧ Source t (packet f j z) (P₀).casts.lanes
        ((P₀).packets.image (P₀).packetBase (u.beforePacketImage ok ((dir).result scene before)))) :
    u.PublicValuesRead ok ((dir).result scene before) x₀ digits numeric issued :=by
  have both:=public_control_operands B previous next u ok grid chart m before (@ran) (@cheap) oldPos newPos oldBits
    actors oldDepth oldLevels depthWidth short
  obtain ⟨stored,dispatch⟩:=both.2 x
  apply u.public_values ok ((dir).result scene before) x₀ R basis ah ag aw ch cg cw left_ right_ packet
    digits numeric captured chosen saved room auxPitch coordPitch packetRead
  · exact ⟨stored.1.1,source_resetRowCast hostFit groupFit controlBits controlPitch _ stored.1.2⟩
  · intro j
    rw [capAt]
    exact ⟨(stored.2 j).1,source_resetRowCast hostFit groupFit controlBits controlPitch _ (stored.2 j).2⟩
  · exact both.1
  · intro i g₀
    have outcome:=dispatch (i.cast hostFit) (g₀.cast groupFit)
    refine ⟨outcome.1,fun hi active=>?_⟩
    let rawRow := (Z).rawAtIndex T rank ⟨i.val, hi⟩
    calc
      _ = (finProdFinEquiv.symm rawRow : Fin oldH × Fin Q).2.val := outcome.2 hi active
      _ = _ := (secondary_cast hRaw sRaw rawRow).symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
