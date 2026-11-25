import OAI.Hierarchy.DescentDatedPublicValues
import OAI.Hierarchy.DescentPublicTreeFields

namespace OAI
/-! # The fallback reader on the actual auxiliary and group/fine register sheet -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentPackedZip DescentSIMDLookup DescentResetOperandSetup DescentColonies ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w) (ok : u.Ready) (actorMem : Memory w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "base" => (v).operandFloor b
local notation "C" => (v).setup
local notation "H" => (C).placement.newHosts
local notation "G" => (C).placement.groups
local notation "m" => u.beforeSetupImage ok actorMem
local notation "s" => (v).sheets
local notation "q" => (s).stemSources.coord
local notation "area" => ((v).remap b).endAddress
local notation "cnt" => (s).metaEnd area
local notation "ceil" => (s).coordinateEnd area
variable (x : Fin a.successor.setup.placement.blocks)
local notation "ctr" => (v).controlRegisters
local notation "cb" => (v).middle.stop b
local notation "start" => (v).controlFloor b
local notation "active" => (ctr).live start x.val
local notation "regs" => (ctr).ports start (a.c/2) x.val (((v).actor.directory cb).inverse)
  ((v).actor.depths cb) ((v).actor.levels cb)
private abbrev rowPorts := OperandMenu.publicPorts (a:=a) u.shape floor u.count u.hub u.g u.Y active regs
local notation "P" => rowPorts u x
variable {N : ℕ} (R : u.MeasuredChannels N)
variable (basis : DescentGL.Layout a.successor.sheets.stemSources.coord.dim)
variable (ah : a.successor.setup.placement.newHosts=a.successor.sheets.hosts)
    (ag : a.successor.setup.placement.groups=a.successor.sheets.groups)
    (aw : a.successor.sheets.metaBits=(rowPorts u x).casts.width 2)
variable (ch : a.successor.setup.placement.newHosts=a.successor.sheets.stemSources.coord.hosts)
    (cg : a.successor.setup.placement.groups=a.successor.sheets.stemSources.coord.groups)
    (cw : a.successor.sheets.stemSources.coord.width=(rowPorts u x).casts.width 1)
variable (live : Fin a.successor.setup.placement.newHosts→Fin a.successor.setup.placement.groups→Cell (rowPorts u x).casts.bits)
    (reg : Fin 4→Fin a.successor.setup.placement.newHosts→Fin a.successor.setup.placement.groups→Cell (rowPorts u x).casts.bits)
variable (packet : (f : Bool)→Fin ((rowPorts u x).packets.stage 0 f).fields→Fin (rowPorts u x).packets.blocks→
    Fin a.successor.setup.placement.newHosts→Fin a.successor.setup.placement.groups→Cell ((rowPorts u x).casts.width 0))

local notation "cfg" => publicOperands u.atlas u.roots u.menu.payload
local notation "F₀" => (cfg).oldConfig
variable (menu : (rowPorts u x).Values a.successor.setup.placement.newHosts a.successor.setup.placement.groups)
    (digits : (rowPorts u x).casts.bits=a.successor.setup.fallbackBits)
variable (issued : menu=u.issuedPublicValues x R basis ah ag aw ch cg cw menu.active menu.register packet)
local notation:max "raw" h:arg band:arg => u.menu.publicData u.shape floor u.count u.hub u.g u.Y active regs menu digits x.val h band
local notation:max "self" h:arg => DescentResetPeerJointPacked.Aux.value (v).front.peer.shapes R.names R.prior R.near ((h).cast ah) 3
local notation:max "low" j:arg => (finProdFinEquiv.symm j : Fin (cfg).donors×Fin (2*(cfg).oldCap)).1.val

include issued in
theorem public_tree_host (h : Fin H) (band : Fin G)
    (numeric : self h<2^(s).metaBits) (paid : self h<2^(P).casts.bits) :
    ((F₀).header ((cfg).basic (raw h band)) 3).val=self h :=by
  have scalar:=(congrArg (fun t : (P).Values H G=>(t.aux 3 h band).val) issued)
  change (menu.aux 3 h band).val=((self h:ℕ):Cell (s).metaBits).val at scalar
  rw [Fin.val_cast_of_lt numeric] at scalar
  exact (u.menu.public_old_host u.shape floor u.count u.hub u.g u.Y active regs menu digits x.val h band
    (scalar.trans_lt paid)).trans scalar

include issued in
theorem public_tree_donor (h : Fin H) (band : Fin G) (row : Fin (F₀).count) (which : Fin 2)
    (inside : x.val<2^(q).fine) (within : low row<2^(q).residual)
    (numeric : (q).value basis which.castSucc ⟨x.val,inside⟩ ⟨_,within⟩ (band.cast cg)<2^(q).width)
    (paid : (q).value basis which.castSucc ⟨x.val,inside⟩ ⟨_,within⟩ (band.cast cg)<2^(P).casts.bits) :
    ((F₀).digit ((cfg).basic (raw h band)) row (which.castLE (by decide : 2≤12))).val=
      (q).value basis which.castSucc ⟨x.val,inside⟩ ⟨_,within⟩ (band.cast cg) :=by
  let lo : Block (q).residual:=⟨_,within⟩
  let current : Block (q).fine:=⟨x.val,inside⟩
  let entry:=(q).value basis which.castSucc current lo (band.cast cg)
  have scalar:=congrArg (fun t : (P).Values H G=>(t.coord which.castSucc current lo h band).val) issued
  change (menu.coord which.castSucc current lo h band).val=((entry:ℕ):Cell (q).width).val at scalar
  rw [Fin.val_cast_of_lt numeric] at scalar
  exact (u.menu.public_donor_word u.shape floor u.count u.hub u.g u.Y active regs menu digits x.val h band row
    which inside within (scalar.trans_lt paid)).trans scalar

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
