import OAI.Hierarchy.TaggedWirePhysicalTerm
import OAI.Hierarchy.TaggedWireTurnOffsets

namespace OAI
/-! # Every route occurrence of a live commodity uses an observed positive native row -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.Report
open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe Tagged WireTelescope
open scoped Classical
variable {h d k w R M den : ℕ} {π : Equiv.Perm (Row h)} {U : Widths (siteLast h d k+1)}
    (Z : Report π d k w R M den U)
local notation "L" => Z.mount.matrixLayout (siteNumber h d k).injective (publicChord h d k)
local notation "cnt" => SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used
local notation "ord" => (L).nativeOrder Z.enum

theorem live_uses_row (i : _) (q : Fin ((L).routes i).length) (pos : 0<cnt i) :
    NativeSlot.start (L).routes cnt ord i q+cnt i≤(Z.rows (((L).routes i).get q)).width := by
  have room:=NativeSlot.start_room (L).routes cnt ord i q pos
  exact room.trans_eq (congrFun (Z.receipt.native_width (siteNumber h d k).injective (publicChord h d k)) _)

theorem live_uses_positive (i : _) (q : Fin ((L).routes i).length) (positive : 0<cnt i) :
    0<(Z.rows (((L).routes i).get q)).width := by
  have room:=Z.live_uses_row i q positive
  omega

theorem live_digit (i : _) (q : Fin ((L).routes i).length) (j : Fin (cnt i)) :
    NativeSlot.start (L).routes cnt ord i q+j.val<(Z.rows (((L).routes i).get q)).width :=
  (Nat.add_lt_add_left j.isLt _).trans_le (Z.live_uses_row i q (Nat.zero_lt_of_lt j.isLt))

end Hierarchy.ProbeStage.CoreBoard.Report

end
end OAI
