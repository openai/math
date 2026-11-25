import OAI.Hierarchy.DescentDatedOperandNativePreparation
import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! # Immutable previous-node, newborn-mouth, and common-digit conversion tables -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedOperandReadPipeline DescentDatedAddressBook DescentStaticWordColumn
open DescentOrdinaryAtomFieldRAM DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)

private theorem page_cost (a n M base w h ratio : ℕ) (fit : (a*n)*M≤ h/2) (bus : w≤ ratio*h) :
    (previousHeaderPhase a n M base w).wordInvoice≤ ratio*(109*h+115*n*2^(h/2)*h) :=by
  change ((4+10*(n*2^((a*n)*M)))+7*names (DescentStaticWordColumn.program w base _ (n*2^((a*n)*M))))*w≤_
  rw [names_mount]
  have power:=Nat.pow_le_pow_right (by decide : 0<2) fit
  calc
    _=(109+115*n*2^((a*n)*M))*w:=by ring
    _≤(109+115*n*2^(h/2))*(ratio*h):=by gcongr
    _=_:=by ring

private theorem cast_cost (width : Fin 4→ℕ) (a M base w h ratio : ℕ)
    (fit : a*M≤ h/2) (bus : w≤ ratio*h) :
    (DescentDatedOperandCasts.phase width a M base w).wordInvoice≤ ratio*(109*h+115*4*2^(h/2)*h) :=by
  change ((4+10*(4*2^(a*M)))+7*names (DescentStaticWordColumn.program w base _ (4*2^(a*M))))*w≤_
  rw [names_mount]
  have power:=Nat.pow_le_pow_right (by decide : 0<2) fit
  calc _=(109+115*4*2^(a*M))*w:=by ring
       _≤(109+115*4*2^(h/2))*(ratio*h):=by gcongr
       _=_:=by ring

variable (prior : DatePorts) (floor w ratio : ℕ)

theorem registered_header_cost (bus : w≤ ratio*v.payload) :
    let W:=v.registeredFrom prior floor
    (W.operandHeaderPhase floor w).wordInvoice+
      (DescentDatedOperandCasts.phase W.operandWidth W.operandShortBits W.resolver.lanes
        (W.headTransferEnd floor) w).wordInvoice≤
      ratio*(327*v.payload+115*(2*W.resolver.nodes+4)*2^(v.payload/2)*v.payload) :=by
  intro W
  let A:=v.registeredEntry prior floor
  let M:=W.resolver.lanes
  let h:=v.payload
  have caps:=v.registered_width prior floor
  have m : M≤ A.clip.working:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have bounded (j : Fin 16) : W.argumentWidths A j*M≤ h/2:=
    ((Nat.mul_le_mul_left _ m).trans (caps.1 j)).trans (by omega)
  have first : ((W.resolver.size+2)*W.resolver.nodes)*M≤ h/2:=bounded 8
  have second : (W.bornBook.bits*W.resolver.nodes)*M≤ h/2:=
    (Nat.mul_le_mul_right M ((le_max_right ..).trans (le_max_left ..))).trans (bounded 14)
  have digit : W.operandShortBits≤ purchase W.ticketReadGeometry:=by
    apply le_trans _ (le_max_left ..)
    change W.operandShortBits≤18*W.operandShortBits;omega
  have trueDigit : W.operandShortBits*M≤ h/2:=((Nat.mul_le_mul_right M digit).trans caps.2).trans (by omega)
  have x:=page_cost (W.resolver.size+2) W.resolver.nodes M (W.operandOldHeaderStart floor) w h ratio first bus
  have y:=page_cost W.bornBook.bits W.resolver.nodes M (W.operandMouthHeaderStart floor) w h ratio second bus
  have z:=cast_cost W.operandWidth W.operandShortBits M (W.headTransferEnd floor) w h ratio trueDigit bus
  unfold operandHeaderPhase
  rw [NativePhase.wordInvoice_seq]
  exact (Nat.add_le_add (Nat.add_le_add x y) z).trans_eq (by dsimp [h];ring)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
