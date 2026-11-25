import OAI.Hierarchy.DescentReachedRotorMatrixData
import OAI.Hierarchy.DescentOperandPreparedPacketPhase

namespace OAI
/-! # Read both halves of the same original operand register at their shared physical parent -/
namespace Hierarchy.DescentOperandRootPull.Pair
open DescentSIMDLookup DescentRotorWindowArchive
open DescentFallbackPeriod DescentFallbackPeriod.Projected
open scoped Classical
noncomputable section
set_option quotPrecheck false

theorem decoded_field_val {a b c d : ℕ} (bits : a=b) (count : c=d) (x : Cell (a*c))
    (row : Fin d→Cell b) (whole : x.val=(encode b d row).val) (j : Fin c) :
    ((encode a c).symm x j).val=(row (j.cast count)).val:=by
  subst b
  subst d
  have read:x=encode a c row:=Fin.ext whole
  rw [read,Equiv.symm_apply_apply]
  rfl

variable (O : DescentOperandRootPull.Pair) {H G field D L cap n r outBits : ℕ}
    (width : O.oldBits=field)
    (fallCount : (O.stage 0 false).fields=inputCount D L cap n r)
    (matCount : (O.stage 0 true).fields=count D L cap)
    (parent : Fin H→Fin O.actors) (band : Fin G→Fin O.blocks→Fin (O.groups*O.blocks))
    (packet : (b:Bool)→Fin (O.stage 0 b).fields→Fin O.blocks→Fin H→Fin G→Cell outBits)
    (previous : (b:Bool)→Fin O.actors→Fin (O.groups*O.blocks)→Cell (O.oldBits*(O.stage 0 b).fields))
    (pulled : ∀b j x h g,(packet b j x h g).val=((encode O.oldBits (O.stage 0 b).fields).symm
        (previous b (parent h) (band g x)) j).val)
    (h : Fin H) (g : Fin G) (x : Fin O.blocks)
    (fallback : Packet D L cap n r field) (board : RowData D L cap field)
    (fall : (previous false (parent h) (band g x)).val=(encodePacket fallback).val)
    (matrix : (previous true (parent h) (band g x)).val=(encode field (count D L cap) fun j=>board (ix.symm j)).val)

include width pulled fall matrix in
/-- The one returned descriptor at a real emitted node yields every original
fallback field, and every original matrix field, at the identical donor. -/
theorem reached_components :
    (∀j : DescentFallbackPeriod.Input D L cap n r,(packet false ((number j).cast fallCount.symm) x h g).val=(fallback j).val) ∧
      ∀j : DescentRotorWindowArchive.Input D L cap,
        (packet true ((ix j).cast matCount.symm) x h g).val=(board j).val:=by
  constructor
  · intro j
    rw [pulled]
    have read:=decoded_field_val width fallCount (previous false (parent h) (band g x)) (fun k=>fallback (number.symm k)) fall
      ((number j).cast fallCount.symm)
    simpa only [Fin.cast_cast,Fin.cast_refl,id_eq,Equiv.symm_apply_apply] using read
  · intro j
    rw [pulled]
    have read:=decoded_field_val width matCount (previous true (parent h) (band g x)) (fun k=>board (ix.symm k)) matrix
      ((ix j).cast matCount.symm)
    simpa only [Fin.cast_cast,Fin.cast_refl,id_eq,Equiv.symm_apply_apply] using read

end
end Hierarchy.DescentOperandRootPull.Pair

end OAI
