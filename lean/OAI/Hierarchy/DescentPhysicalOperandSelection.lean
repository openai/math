import OAI.Hierarchy.DescentPhysicalPublicOperandInputs
import OAI.Hierarchy.DescentResetControlRegisterWords
import OAI.Hierarchy.DescentResetOperandMovedSources
import OAI.Hierarchy.DescentDatedResetOperands

namespace OAI
/-! Operand requests for the successor's compact argument slots. -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup DescentPackedZip ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (C : DescentResetOperandSetup.Chart) (base : ℕ)

def oldField (x : Fin C.placement.blocks) (i : Fin C.retained.outputs) : Expr :=
  .lookup (C.seven.bank base i x) .row
def portField (x : Fin C.placement.blocks) (i : Fin C.strip) : Expr :=
  .lookup (C.placement.bank C.signedFields (C.placedSigned base) i x) .row
def converted (i : Fin C.inputs) (e : Expr) : Expr :=
  DescentOperandInputCast.expr C.width C.fieldBits C.sourceWidth C.lanes (C.publicEnd base) i e

/-- The old operand digit and donor label travel through the same retained placement.
The hub and ticket have already been converted to the width of the corrected cable. -/
def carried (x : Fin C.placement.blocks) (arg : Fin C.retained.args) (node : Fin C.retained.nodes)
    (hub : Expr) (ticket : Fin C.strip→Expr) (i : Fin C.inputs) : Expr :=
  if h:i.val<4 then
    C.converted base i (C.oldField base x (C.retained.outputID 0 ⟨i.val,by omega⟩ arg node))
  else if h4 : i.val=4 then
    C.converted base i (C.oldField base x (C.retained.donorID node))
  else if h5 : i.val=5 then hub
  else if h:i.val<6+C.strip then
    C.converted base i (C.portField base x ⟨i.val-6,by omega⟩)
  else
    ticket ⟨i.val-(6+C.strip),by have hi:i.val<6+2*C.strip:=i.isLt;omega⟩

def oldValue (x : Fin C.placement.blocks) (arg : Fin C.retained.args) (node : Fin C.retained.nodes)
    (f : Fin 7) : Expr :=
  C.converted base ⟨0,by unfold inputs;omega⟩ (C.oldField base x (C.retained.outputID 1 f arg node))

def selected (laws : C.Laws) (mode : Option (Fin 7)) (x : Fin C.placement.blocks)
    (arg : Fin C.retained.args) (node : Fin C.retained.nodes) (old : Fin C.inputs→Expr)
    (rotor : Fin 4→Expr) (public_ : Fin C.fallbackInputs→Expr) : Expr :=
  let j : Fin C.members:=finProdFinEquiv (arg,node)
  match mode with
  | none=>
    let cable:=DescentOperandFamilyBook.expr C.cable.queryLaw C.lanes (C.casts base) 0 old
    let root:=DescentOperandFamilyBook.expr laws.rotorQuery C.lanes (C.rotorQuery base) j rotor
    let surface:=DescentOperandFamilyBook.expr laws.fallbackQuery C.lanes (C.fallbackQuery base) j public_
    .op .add cable (.op .add root surface)
  | some f=>
    let oldValue:=C.oldValue base x arg node f
    let correct:=if f=2 ∨ f=3 then
        DescentOperandFamilyBook.expr C.cable.prices C.lanes (C.find base) (if f=2 then 0 else 1) old
      else .lit 0
    let idx:=finProdFinEquiv (f,j)
    let root:=DescentOperandFamilyBook.expr laws.rotorFields C.lanes (C.rotorFields base) idx rotor
    let surface:=DescentOperandFamilyBook.expr laws.fallbackFields C.lanes (C.fallbackFields base) idx public_
    .op .add (.op .add oldValue correct) (.op .add root surface)

end
end Hierarchy.DescentResetOperandSetup.Chart

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentResetOperandSetup ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
set_option quotPrecheck false
local notation "v" => a.successor
local notation "C" => (v).setup

def renderer (floor : ℕ) (sh : a.StencilShape) (count hub : Bank) (g Y : ℕ)
    (block : (v).receiver.blocks=(C).placement.blocks)
    (channels : (v).receiver.fields=((7*(C).retained.args)*(v).receiver.blocks)*(C).retained.nodes)
    (hubAt : Fin (C).placement.blocks→Expr) (ticketAt : Fin (C).placement.blocks→Fin (C).strip→Expr) :
    (v).OperandInputs :=
  let b:=a.rebased floor
  let begin₀:=(v).middle.stop b
  let actor:=(v).actor
  let liveAt:=(v).controlFloor b
  let ctrl:=(v).controlRegisters
  let decode:=(((finProdFinEquiv.prodCongr (Equiv.refl (Fin (v).receiver.blocks))).trans finProdFinEquiv).prodCongr
    (Equiv.refl (Fin (C).retained.nodes))).trans (finProdFinEquiv.trans (Equiv.cast (congrArg Fin channels.symm)))
  let issue:=fun (query : Bool) (i : Fin (v).receiver.fields)=>
    let t : ((Fin 7×Fin (C).retained.args)×Fin (v).receiver.blocks)×Fin (C).retained.nodes:=decode.symm i
    let x:=t.1.2.cast block
    let live:=ctrl.live liveAt x.val
    let registers:=ctrl.ports liveAt (a.c/2) x.val (actor.directory begin₀).inverse (actor.depths begin₀) (actor.levels begin₀)
    let public_:=menu.publicInput sh floor count hub g Y live registers x.val
    let old:=(C).carried ((v).operandFloor b) x t.1.1.2 t.2 (hubAt x) (ticketAt x)
    (C).selected ((v).operandFloor b) menu.tables (if query then none else some t.1.1.1)
      x t.1.1.2 t.2 old registers public_
  ⟨(C).retained.args,(C).retained.nodes,channels,(v).receiver.valueBits,issue true,issue false⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
