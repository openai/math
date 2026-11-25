import OAI.Hierarchy.DescentDatedPublicCoordinateRows
import OAI.Hierarchy.DescentDatedPublicMenuRows
import OAI.Hierarchy.DescentResetRecordedPrimary

namespace OAI
/-! The five mounted input families of the public operand lookup, on the same reset. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentPackedZip DescentSIMDLookup DescentResetOperandSetup DescentColonies ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

def resetRowCast {H G bits H' G' bits' : ℕ} (hh : H'=H) (gg : G'=G) (bb : bits=bits')
    (f : Fin H→Fin G→Cell bits) (h : Fin H') (g : Fin G') : Cell bits' :=
  (f (h.cast hh) (g.cast gg)).cast (congrArg (2^·) bb)

theorem source_resetRowCast {H G bits M H' G' bits' M' w : ℕ} {e : Expr} {m : Memory w}
    (hh : H'=H) (gg : G'=G) (bb : bits=bits') (mm : M=M') (f : Fin H→Fin G→Cell bits)
    (read : Source e f M m) : Source e (resetRowCast hh gg bb f) M' m :=by
  subst H';subst G';subst bits';subst M';exact read

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

def issuedPublicValues : (P).Values H G where
  «active» := live
  register:=reg
  aux j:=resetRowCast ah ag aw (fun (h : Fin (s).hosts) (_ : Fin (s).groups) =>
    (DescentResetPeerJointPacked.Aux.value (v).front.peer.shapes R.names R.prior R.near h j : Cell (s).metaBits))
  coord j block lo:=resetRowCast ch cg cw (fun (_:Fin (q).hosts) g=>((q).value basis j block lo g : Cell (q).width))
  packet:=packet

local notation "values" => u.issuedPublicValues x R basis ah ag aw ch cg cw live reg packet
local notation "cfg" => publicOperands u.atlas u.roots u.menu.payload
variable (digits : (rowPorts u x).casts.bits=a.successor.setup.fallbackBits)
local notation "payload" => u.menu.publicData u.shape floor u.count u.hub u.g u.Y active regs values digits x.val
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)

/-- Seven obligations consumed together by the native seven-column operand reader. -/
def PublicValuesRead (rows : (P).Values H G) : Prop :=
    (∀j,((P).aux j).Fits w base ∧ Source ((P).aux j) (rows.aux j) (P).casts.lanes m) ∧
    (∀j z lo,let t:=(P).coordinates.src (P).coordinateBase (P).saved j z lo
      t.Fits w base ∧ Source t (rows.coord j z lo) (P).casts.lanes m) ∧
    (∀f j z,let t:=(P).packets.src (P).packetBase f j z
      t.Fits w (P).castBase ∧ Source t (rows.packet f j z) (P).casts.lanes ((C).packetMemory base u.bank m)) ∧
    ((active).Fits w base ∧ Source active rows.active (P).casts.lanes m) ∧
    (∀j,(regs j).Fits w base ∧ Source (regs j) (rows.register j) (P).casts.lanes m) ∧
    (∀h g,((cfg).oldConfig.header ((cfg).basic (u.menu.publicData u.shape floor u.count u.hub u.g u.Y active regs rows digits x.val h g)) 0).val=0 → ((cfg).reg (u.menu.publicData u.shape floor u.count u.hub u.g u.Y active regs rows digits x.val h g) 1).val=0) ∧
    (∀h g (hv:h.val<U),((cfg).oldConfig.header ((cfg).basic (u.menu.publicData u.shape floor u.count u.hub u.g u.Y active regs rows digits x.val h g)) 0).val≠0 →
       ((cfg).reg (u.menu.publicData u.shape floor u.count u.hub u.g u.Y active regs rows digits x.val h g) 3).val=((C).placement.shape (name ⟨h.val,hv⟩)).val)


attribute [local irreducible] DescentPackedZip.Source

theorem public_values (captured : CaptureRoom R actorMem)
    (chosen : u.masked.image (u.privateResult actorMem) u.originalBasis.base=((DescentExterior.matrixCode basis).val:Word w))
    (saved : u.originalBasis.Fits w cnt) (space : ceil<2^w)
    (auxPitch : (s).lanes=(P).casts.lanes) (coordPitch : (q).lanes=(P).casts.lanes)
    (packetRead : ∀f j z,let t:=(P).packets.src (P).packetBase f j z
      t.Fits w (P).castBase ∧ Source t (packet f j z) (P).casts.lanes
        ((P).packets.image (P).packetBase (u.beforePacketImage ok actorMem)))
    (control : (active).Fits w base ∧ Source active live (P).casts.lanes (u.sheetsResult ok actorMem))
    (ports : ∀j,(regs j).Fits w base ∧ Source (regs j) (reg j) (P).casts.lanes (u.sheetsResult ok actorMem))
    (kept : ∀z,z<base→u.sheetsResult ok actorMem z=m z)
    (dispatch : ∀h g,((live h g).val=0 → (reg 1 h g).val=0) ∧
      ∀hv : h.val<U,(live h g).val≠0 → (reg 3 h g).val=((C).placement.shape (name ⟨h.val,hv⟩)).val) :
    u.PublicValuesRead ok actorMem x digits name values :=by
  have restore {t : Expr} {vals : Fin H→Fin G→Cell (P).casts.bits}
      (s₀ : t.Fits w base ∧ Source t vals (P).casts.lanes (u.sheetsResult ok actorMem)) :
      t.Fits w base ∧ Source t vals (P).casts.lanes m := by
    unfold Source at s₀ ⊢
    exact ⟨s₀.1,fun p=>(eval_below t _ _ m s₀.1 (fun z h=>(kept z h).symm)).trans (s₀.2 p)⟩
  have header (h g) : ((cfg).oldConfig.header ((cfg).basic (payload h g)) 0).val=(live h g).val:=
    u.menu.public_header_register u.shape floor u.count u.hub u.g u.Y active regs values digits x.val h g 0
  have register (j h g) : ((cfg).reg (payload h g) j).val=(reg j h g).val:=
    u.menu.public_control_registers u.shape floor u.count u.hub u.g u.Y active regs values digits x.val h g j
  refine ⟨?_,?_,packetRead,restore control,fun j=>restore (ports j),?_,?_⟩
  · intro j
    have r:=u.public_auxiliary_rows R ok actorMem captured j
    exact ⟨r.1,source_resetRowCast ah ag aw auxPitch _ r.2⟩
  · intro j z lo
    have r:=u.public_coordinate_rows ok actorMem basis chosen saved space j z lo
    exact ⟨r.1,source_resetRowCast ch cg cw coordPitch _ r.2⟩
  · intro h g blank
    exact (register 1 h g).trans ((dispatch h g).1 ((header h g).symm.trans blank))
  · intro h g hv seen
    exact (register 3 h g).trans ((dispatch h g).2 hv (fun zero=>seen ((header h g).trans zero)))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
