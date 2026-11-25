import OAI.Hierarchy.DescentDatedOperandTableFrame
import OAI.Hierarchy.DescentPublicOperandRows

namespace OAI
/-! # The two realized menu outputs on the final reset tape -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentPackedZip DescentSIMDLookup DescentResetOperandSetup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "floor₀" => (v).operandFloor b
local notation "actor" => (v).actor
local notation "begin₀" => (v).middle.stop b
local notation "start" => (v).controlFloor b
local notation "C" => (v).setup
local notation "ctrl" => (v).controlRegisters
local notation "cfg" => publicOperands u.atlas u.roots u.menu.payload
variable (x : Fin a.successor.setup.placement.blocks)
local notation "active" => (ctrl).live start x.val
local notation "reg" => (ctrl).ports start (a.c/2) x.val ((actor).directory begin₀).inverse ((actor).depths begin₀) ((actor).levels begin₀)
local notation "P" => OperandMenu.publicPorts (a:=a) u.shape floor u.count u.hub u.g u.Y active reg

theorem dated_public_menu {H G} (values : (P).Values H G) (ok : u.Ready) (atActors : Memory w)
    (digits : (P).casts.bits=(C).fallbackBits) (lanes : (P).casts.lanes=(C).lanes)
    (aux : ∀j,((P).aux j).Fits w floor₀ ∧ Source ((P).aux j) (values.aux j) (P).casts.lanes (u.beforeSetupImage ok atActors))
    (coords : ∀j x lo,let e:=(P).coordinates.src (P).coordinateBase (P).saved j x lo
      e.Fits w floor₀ ∧ Source e (values.coord j x lo) (P).casts.lanes (u.beforeSetupImage ok atActors))
    (packet : ∀f j x,let e:=(P).packets.src (P).packetBase f j x
      e.Fits w (P).castBase ∧ Source e (values.packet f j x) (P).casts.lanes
        ((P).packets.image (P).packetBase (u.beforePacketImage ok atActors)))
    (live : (active).Fits w floor₀ ∧ Source active values.active (P).casts.lanes (u.beforeSetupImage ok atActors))
    (registers : ∀i,(reg i).Fits w floor₀ ∧ Source (reg i) (values.register i) (P).casts.lanes (u.beforeSetupImage ok atActors))
    (arg : Fin (C).retained.args) (node : Fin (C).retained.nodes) :
    let src:=u.menu.publicInput u.shape floor u.count u.hub u.g u.Y active reg x.val
    let payload:=u.menu.publicData u.shape floor u.count u.hub u.g u.Y active reg values digits x.val
    let mouth:=finProdFinEquiv (arg,node)
    (let e:=DescentOperandFamilyBook.expr u.laws.fallbackQuery (C).lanes ((C).fallbackQuery floor₀) mouth src
     e.Fits w ((v).operandStart b) ∧
       Source e (fun h g=>(cfg).column u.atlas.board (C).queryBits none mouth (payload h g)) (C).lanes (u.sheetsResult ok atActors)) ∧
    (∀f : Fin 7,let e:=DescentOperandFamilyBook.expr u.laws.fallbackFields (C).lanes ((C).fallbackFields floor₀) (finProdFinEquiv (f,mouth)) src
       e.Fits w ((v).operandStart b) ∧
       Source e (fun h g=>(cfg).column u.atlas.board (C).fieldBits (some f) mouth (payload h g)) (C).lanes (u.sheetsResult ok atActors)) :=by
  have before:=(v).operand_order b
  have ordered := (v).keep_before b
  have room:=(ordered.trans ((before.1.trans before.2).trans ((v).final_ge b))).trans_lt ok.full
  have r:=u.menu.public_columns u.shape floor u.count u.hub u.g u.Y active reg values
    (u.beforeSetupImage ok atActors) digits lanes ok.placed room aux coords packet live registers x.val arg node
  exact ⟨⟨ProtocolRAMGeneratedWrite.fits_mono _ ordered r.1.1,u.operand_page_source ok atActors _ _ _ r.1.1 r.1.2⟩,
    fun i=>⟨ProtocolRAMGeneratedWrite.fits_mono _ ordered (r.2 i).1,u.operand_page_source ok atActors _ _ _ (r.2 i).1 (r.2 i).2⟩⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
