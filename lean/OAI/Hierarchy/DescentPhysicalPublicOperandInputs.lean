import OAI.Hierarchy.DescentPublicOperandInputs
import OAI.Hierarchy.DescentPhysicalOperandMenu
import OAI.Hierarchy.DescentPhysicalResetOriginalSeries
import OAI.Hierarchy.DescentPhysicalResetJointScene
import OAI.Hierarchy.DescentDatedWholeOperands

namespace OAI
/-! # Actual dated banks supplying the public reset operand menu -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open ProtocolRAM DescentResetPublicOperandBook DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (m : OperandMenu z roots)
namespace OperandMenu
set_option quotPrecheck false
local notation "v" => a.successor
local notation "C" => (v).setup
local notation "s" => (v).sheets
local notation "mesh" => (v).middle

def publicPorts (sh : a.StencilShape) (start : ℕ) (count hub : Bank) (g Y : ℕ)
    (active : Expr) (reg : Fin 4→Expr) : DescentResetPublicOperandBook.Ports :=
  let b:=a.rebased start
  let rbase:=((v).remap b).endAddress
  let operand:=(v).operandFloor b
  {packets:=(C).packets,coordinates:=(s).stemSources.coord,casts:=(C).publicCasts,
   saved:=⟨(a.stencilPhase sh start count hub g Y).saved,0⟩,
   coordinateBase:=(s).metaEnd rbase,packetBase:=(C).placed operand,castBase:=(C).packetEnd operand,
   aux:=(v).peerAux b,active:=active,registers:=reg}

theorem publicInputIndex : (C).fallbackInputs=(publicOperands z roots m.payload).inputs (mesh).rotorBits :=
  m.inputCount.trans (Chart.public_arity ..).symm

def publicInput (sh : a.StencilShape) (start : ℕ) (count hub : Bank) (g Y : ℕ)
    (active : Expr) (registers : Fin 4→Expr) (x : ℕ) (j : Fin (C).fallbackInputs) : Expr :=
  let cfg:=publicOperands z roots m.payload
  let number : (C).fallbackInputs=cfg.inputs (mesh).rotorBits:=
    m.publicInputIndex
  (publicPorts sh start count hub g Y active registers).publicInput cfg x (j.cast number)

end OperandMenu
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
