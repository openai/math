import OAI.Hierarchy.DescentOrdinaryWordTariff
import OAI.Hierarchy.DescentDatedNodeMetadataVolume

namespace OAI
/-! # Both ordinary node-metadata columns are charged at the public bus width -/
namespace Hierarchy.DescentDatedNodeMetadata.Chart
open DescentPacking.PackedMatch.Local
open DescentSIMDLookup DescentStaticWordColumn ProtocolRAM
noncomputable section
variable {K : ℕ} (v : DescentDatedNodeMetadata.Chart)

theorem ordinaryWordVolume (floor a b w h u q ratio R : ℕ) (paid : v.Counts) (src : v.Vectors K)
    (positive : 0<u) (wide : 2*u≤h) (bus : w≤ratio*h) (nodeBits : (v.bits*v.nodes+v.bits)*v.lanes≤h/2)
    (countBits : max a (b+v.bits)*v.lanes≤h/2) (priorBits : (b*v.nodes)*v.lanes≤h/2)
    (physical : v.rows≤R*Stage.DateBill.words v.hosts v.groups h u) (cheap : ∀x,(paid x).work≤q) :
    let work:=tallyWork K (max q 16)
    Stage.DateBill.bitTariff (v.ordinaryProgram floor a b w paid src) (v.ordinaryTime floor a b paid src)≤
      (2*ratio*(((4+10*v.nodes)+(v.inputClock+v.loopUnits R work))+
        7*(15*(v.nodes+1)+(v.inputNames+v.labelUnits work))))*Stage.DateBill.volumeBits v.hosts v.groups h u :=by
  intro work
  let U:=Stage.DateBill.words v.hosts v.groups h u
  have dir : 2^(h/2)≤U:=by dsimp [U,Stage.DateBill.words];omega
  have pos : 1≤U:=(Nat.two_pow_pos _).trans_le dir
  have goal_:=v.wordInvoices U h a b work R pos dir nodeBits countBits physical
  have initial : v.digitWords b≤v.nodes*U:=Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) priorBits).trans dir)
  have bill:=v.ordinaryPrice floor a b w q paid src cheap
  apply Stage.DateBill.from_words _ _ _ _ _ _ _ _ _ positive wide bus
  · apply bill.1.trans
    rw [Nat.add_mul]
    apply Nat.add_le_add _ goal_.1
    calc
      _ ≤ 4*U+10*(v.nodes*U):=Nat.add_le_add (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 4 pos) (Nat.mul_le_mul_left _ initial)
      _ = _:=by ring
  · apply bill.2.trans
    rw [Nat.add_mul]
    apply Nat.add_le_add _ goal_.2
    calc
      _ ≤ 15*(v.nodes*U+U):=Nat.mul_le_mul_left _ (Nat.add_le_add initial pos)
      _ = _:=by ring

end
end Hierarchy.DescentDatedNodeMetadata.Chart

end OAI
