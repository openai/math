import OAI.Hierarchy.DescentDatedRotorSerialVolume

namespace OAI
/-! Bound the rotor serial on the actual issued public menu at every row of the
native cast pages, including padded rows, from its one returned capacity word. -/
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
variable (hostFit : nativeH=H) (groupFit : nativeG=J)
    (menuRows : (P₀).Values nativeH nativeG) (digits : (P₀).casts.bits=(C₀).fallbackBits)
local notation "cfg" => PhysicalReset.publicOperands u.atlas u.roots u.menu.payload
local notation "record" => u.menu.publicData u.shape floor u.count u.hub u.g u.Y live_ reg_ menuRows digits x.val

/-- The zero-th scalar of the four physical registers is the previous capacity
on an occupied host and zero wherever the controller masked its row. -/
theorem issued_menu_capacity (h₁ : Fin nativeH) (g₁ : Fin nativeG)
    (word : (menuRows.register 0 h₁ g₁).val=((c₀).enabled (values x)
      (controlScalar B previous next 0) (h₁.cast hostFit) (g₁.cast groupFit)).val) :
    ((cfg).reg (record h₁ g₁) 0).val≤cap :=by
  rw [u.menu.public_control_registers u.shape floor u.count u.hub u.g u.Y live_ reg_
    menuRows digits x.val h₁ g₁ 0,word]
  unfold DescentResetControlRegisters.Chart.enabled
  split
  · exact Nat.zero_le _
  · change ((controlReceiver B next (h₁.cast hostFit)).elim 0 (fun _ => cap)) % 2^a₀ ≤ cap
    cases controlReceiver B next (h₁.cast hostFit) with
    | none => exact Nat.zero_le _
    | some _ => exact Nat.mod_le _ _

theorem issued_menu_rotor_volume (h₁ : Fin nativeH) (g₁ : Fin nativeG) (node arg : ℕ)
    (word : (menuRows.register 0 h₁ g₁).val=((c₀).enabled (values x)
      (controlScalar B previous next 0) (h₁.cast hostFit) (g₁.cast groupFit)).val)
    (packetRoom : u.atlas.packet≤2^A.depthCut) (budget : reserveGain u.atlas.boardDegree u.atlas.C A.depthCut≤S.capGain) :
    ((cfg).rotor.flatReg u.atlas.board (cfg).multiplicity (cfg).grain (cfg).split node arg
      (2:Fin 7).succ ((cfg).reg (record h₁ g₁)):Cell (C₀).fieldBits).val≤DescentOperandWidth.publicCap S :=by
  let prior:=2^(8+S.capGain*i)
  have positive:0<prior:=Nat.two_pow_pos _
  have src:((cfg).reg (record h₁ g₁) 0).val≤prior:=
    (issued_menu_capacity (B:=B) (previous:=previous) (next:=next) (u:=u) (x:=x) (hostFit:=hostFit)
      (groupFit:=groupFit) (menuRows:=menuRows) (digits:=digits) h₁ g₁ word).trans old.valid.capacity
  have charge:=(cfg).rotor.flat_serial_reserve u.atlas.board (cfg).multiplicity (cfg).grain (cfg).split node arg prior
    ((cfg).reg (record h₁ g₁)) rfl positive src packetRoom
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

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
