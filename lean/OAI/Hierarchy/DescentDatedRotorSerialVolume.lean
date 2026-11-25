import OAI.Hierarchy.DescentDatedPublicQueryRoom
import OAI.Hierarchy.DescentRotorSerialVolume
import OAI.Hierarchy.DescentIssuedSerialCap

namespace OAI
/-! The real masked capacity register pays every rotor serial, including padded coordinates. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentDenseHostOrder DescentActorRaster
open DescentPackedZip DescentSIMDLookup DescentPackedColony DescentDatedAddressBook DescentResetControlRegisters
open DescentVenueQuantityPlanes
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
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

variable (x : DescentColonies.Block k) (blockCount : 2^k=(C₀).placement.blocks)
local notation "x₀" => x.cast blockCount
local notation "live_" => (V₀).controlRegisters.live start x.val
local notation "reg_" => (V₀).controlRegisters.ports start (A.c/2) x.val ((U₀).directory cb).inverse depths levels
local notation "P₀" => PhysicalReset.OperandMenu.publicPorts (a:=A) u.shape floor u.count u.hub u.g u.Y live_ reg_
variable (hostFit : nativeH=H) (groupFit : nativeG=J) (controlBits : a₀=(P₀).casts.bits)
variable (controlPitch : M=(P₀).casts.lanes) (capAt : A.c/2=cap)
variable (hRaw : oldH=(C₀).placement.oldHosts) (sRaw : Q=(C₀).placement.shapes)
local notation "numeric" => (fun j=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hRaw sRaw))
local notation "left_" => resetRowCast hostFit groupFit controlBits ((c₀).enabled (values x) (fun _=>1))
local notation "right_" => (fun j : Fin 4=>resetRowCast hostFit groupFit controlBits ((c₀).enabled (values x)
   (controlScalar B previous next j)))
variable {N : ℕ} (R : u.MeasuredChannels N) (basis : DescentGL.Layout (coord).dim)
variable (ah : nativeH=(S₀).hosts) (ag : nativeG=(S₀).groups) (aw : (S₀).metaBits=(P₀).casts.width 2)
variable (ch : nativeH=(coord).hosts) (cg : nativeG=(coord).groups) (cw : (coord).width=(P₀).casts.width 1)
variable (digits : (P₀).casts.bits=(C₀).fallbackBits)
variable (packet : (f : Bool)→Fin ((P₀).packets.stage 0 f).fields→Fin (P₀).packets.blocks→
    Fin nativeH→Fin nativeG→Cell ((P₀).casts.width 0))
local notation "issued" => u.issuedPublicValues x₀ R basis ah ag aw ch cg cw left_ right_ packet


local notation "cfg" => PhysicalReset.publicOperands u.atlas u.roots u.menu.payload
local notation "rowData" => u.menu.publicData u.shape floor u.count u.hub u.g u.Y live_ reg_ issued digits x.val

theorem measured_capacity_le (h₁ : Fin nativeH) (g₁ : Fin nativeG) :
    ((cfg).reg (rowData h₁ g₁) 0).val≤cap:=by
  rw [u.menu.public_control_registers u.shape floor u.count u.hub u.g u.Y live_ reg_
    issued digits x.val h₁ g₁ 0]
  let h':=h₁.cast hostFit
  let g':=g₁.cast groupFit
  change ((c₀).enabled (values x) (controlScalar B previous next 0) h' g').val≤cap
  unfold DescentResetControlRegisters.Chart.enabled
  split
  · exact Nat.zero_le _
  · change ((controlReceiver B next h').elim 0 (fun _ => cap)) % 2^a₀ ≤ cap
    cases controlReceiver B next h' with
    | none => exact Nat.zero_le _
    | some _ => exact Nat.mod_le _ _

theorem dated_rotor_serial_volume (h₁ : Fin nativeH) (g₁ : Fin nativeG) (node arg : ℕ)
    (packetRoom : u.atlas.packet≤2^A.depthCut)
    (budget : reserveGain u.atlas.boardDegree u.atlas.C A.depthCut≤S.capGain) :
    ((cfg).rotor.flatReg u.atlas.board (cfg).multiplicity (cfg).grain (cfg).split node arg
       (2:Fin 7).succ ((cfg).reg (rowData h₁ g₁)):Cell (C₀).fieldBits).val≤DescentOperandWidth.publicCap S:=by
  let prior:=2^(8+S.capGain*i)
  have positive : 0<prior:=Nat.two_pow_pos _
  have src:((cfg).reg (rowData h₁ g₁) 0).val≤prior :=
    (measured_capacity_le B previous next u x blockCount hostFit groupFit controlBits R basis ah ag aw ch cg cw
      digits packet h₁ g₁).trans old.valid.capacity
  have charge:=(cfg).rotor.flat_serial_reserve u.atlas.board (cfg).multiplicity (cfg).grain (cfg).split node arg prior
    ((cfg).reg (rowData h₁ g₁)) rfl positive src packetRoom
  apply (Nat.mod_le ..).trans (charge.trans ?_)
  calc
    2^reserveGain u.atlas.boardDegree u.atlas.C A.depthCut*prior ≤2^S.capGain*prior :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) budget)
    _ = 2^(8+S.capGain*(i+1)):=by
      dsimp only [prior]
      rw [←pow_add,Nat.mul_succ]
      congr 1
      omega
    _ ≤ _:=Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_left _ B.age) _)

theorem scheduled_rotor_format :
    rates.bitsR≤2^f ∧ reserveGain h C f≤S.capGain :=by
  refine ⟨(Nat.le_mul_of_pos_left _ (pow_pos (Nat.two_pow_pos n) 2)).trans rates.rows,?_⟩
  simpa only [←rates.gain] using rates.cap

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
