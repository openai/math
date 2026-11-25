import OAI.Hierarchy.DescentCalendarPublicValues
import OAI.Hierarchy.DescentNativePublicQueryBound

namespace OAI
/-! # The actual reset capacity on every occupied compact receiver -/
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


local notation "cfg" => PhysicalReset.publicOperands u.atlas u.roots u.menu.payload
local notation "rowData" => u.menu.publicData u.shape floor u.count u.hub u.g u.Y live_ reg_ issued digits x.val

/-- Source register zero carries the old cap wherever the physical receiver mask is on,
even on a partially filled last packed word. -/
theorem measured_capacity (h₁ : Fin nativeH) (g₁ : Fin nativeG) (capRoom : cap<2^a₀)
    (seen : ((cfg).oldConfig.header ((cfg).basic (rowData h₁ g₁)) 0).val≠0) :
    ((cfg).reg (rowData h₁ g₁) 0).val=cap :=by
  have headerRead :=u.menu.public_header_register u.shape floor u.count u.hub u.g u.Y live_ reg_
    issued digits x.val h₁ g₁ 0
  have out:=u.menu.public_control_registers u.shape floor u.count u.hub u.g u.Y live_ reg_
    issued digits x.val h₁ g₁ 0
  let h':=h₁.cast hostFit
  let g':=g₁.cast groupFit
  have used : actualBit B next h' g' x≠0:=by
    intro zero
    apply seen
    rw [headerRead]
    change (((c₀).enabled (values x) (fun _=>1) h' g').val)=0
    simp [DescentResetControlRegisters.Chart.enabled,zero]
  obtain ⟨v,atHost⟩ : ∃v,controlReceiver B next h'=some v:=by
    cases hv : controlReceiver B next h' with
    | none => exact (used (control_receiver_none B next h' hv g' x)).elim
    | some v => exact ⟨v,rfl⟩
  have controlZero : controlScalar B previous next 0 h' = cap := by
    unfold controlScalar
    rw [atHost]
    rfl
  rw [out]
  change ((c₀).enabled (values x) (controlScalar B previous next 0) h' g').val=cap
  simp only [DescentResetControlRegisters.Chart.enabled, ite_eq_right used]
  exact (congrArg (fun n : ℕ => (n : Cell a₀).val) controlZero).trans (Fin.val_cast_of_lt capRoom)

include capAt in
/-- Bound on the native query word at the actual reset before scattering its seven fields. -/
theorem dated_public_query_room (h₁ : Fin nativeH) (g₁ : Fin nativeG)
    (capRoom : cap<2^a₀) (j : Fin (cfg).oldConfig.mouths) :
    ((cfg).column u.atlas.board (C₀).queryBits none j (rowData h₁ g₁)).val≤
      2*DescentResetLocalRoster.publicSlots u.atlas.board u.roots.Ht (V₀).middle.rootDepth (A.c/2) :=by
  apply DescentResetOperandSetup.Chart.public_query_room
  intro seen
  exact (measured_capacity B previous next u x blockCount hostFit groupFit controlBits R basis ah ag aw ch cg cw
    digits packet h₁ g₁ capRoom seen).trans capAt.symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
