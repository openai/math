import OAI.Hierarchy.DescentPrivateMaskPeriodPrice
import OAI.Hierarchy.DescentResetReceivedVolume
import OAI.ThreeFlat.Routing.CallBatches

namespace OAI
/-! The private mask dictionaries are shared by every old rack and every projected field. -/
namespace Hierarchy.DescentPrivateMaskDeck.Shape
open DescentSIMDLookup DescentDatedAddressBook
open ThreeFlat.Routing
noncomputable section

def volumeFactor (a : Shape) :=
  50000*(a.cap+1)*(a.fields+1)*(a.shapes+1)*(a.blocks+2)

theorem period_volume (a : Shape) (h : ℕ) (same : a.oldBatch=a.batch)
    (positive : 0 < a.batch) (blocks : 0 < a.blocks) (lanes : a.oldBatch ≤ h)
    (panels : a.panels*a.oldBatch ≤ h/2) (old : a.metaBits*a.oldBatch ≤ h/2)
    (project : (a.metaBits*a.blocks)*a.batch ≤ h/2) :
    a.periodPrice ≤ a.volumeFactor*ResetOutput.receiptArea h a.oldHosts
      (chunks (a.groups*a.blocks) a.oldBatch) :=by
  let T:=ResetOutput.receiptArea h a.oldHosts (chunks (a.groups*a.blocks) a.oldBatch)
  let H:=a.oldHosts*a.shapes
  let N:=a.fields
  let X:=a.blocks
  let M:=a.batch
  let G:=a.groups
  have shared : (h+1)^3*2^(h/2) ≤ T:=Nat.le_add_left ..
  have one : 1 ≤ T := (show 1 ≤ (h+1)^3*2^(h/2) from Nat.mul_pos (by positivity) (by positivity)).trans shared
  have cube : h+1≤(h+1)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos h) (by decide : 1 ≤ 3)
  have page : 2^(h/2) ≤ T:=(Nat.le_mul_of_pos_left _ (by positivity : 0<(h+1)^3)).trans shared
  have stock : a.count≤3*a.cap*T :=by
    unfold count words
    rw [Nat.mul_comm 3 a.cap]
    gcongr
    exact (Nat.pow_le_pow_right (by decide) panels).trans page
  have row_base : a.oldHosts*chunks (G*X) a.oldBatch ≤ T:=by dsimp [T,ResetOutput.receiptArea,G,X];omega
  have few : G ≤ G*X:=Nat.le_mul_of_pos_right _ blocks
  have groupRows : chunks G M ≤ chunks (G*X) a.oldBatch:=by
    rw [same];exact Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right few _) _)
  have oldRows : H*chunks (G*X) a.oldBatch ≤ a.shapes*T:=by
    simpa only [H,Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left a.shapes row_base
  have groupCount : H*chunks G M ≤ a.shapes*T:=(Nat.mul_le_mul_left H groupRows).trans oldRows
  have crossed : chunks (G*X) (M*X) ≤ chunks G M:=by
    change (G*X) ⌈/⌉ (M*X) ≤ _
    apply (ceilDiv_le_iff_le_mul (Nat.mul_pos positive blocks)).2
    calc G*X≤(M*chunks G M)*X:=Nat.mul_le_mul_right _ (CallPool.count_le_batches_mul G M positive)
         _=M*X*chunks G M:=by ring
  have parts : Overlap.pieces (G*X) a.oldBatch (M*X)+1 ≤ X+2 :=by
    have raw : chunks (M*X) a.oldBatch ≤ X:=by
      change (M*X) ⌈/⌉ a.oldBatch ≤ X
      rw [same]
      exact (ceilDiv_le_iff_le_mul positive).2 le_rfl
    exact Nat.succ_le_succ ((min_le_right ..).trans (Nat.succ_le_succ raw))
  have dictionary : (Overlap.pieces (G*X) a.oldBatch (M*X)+1)*(a.oldBatch+1)*2^(a.metaBits*a.oldBatch)≤(X+2)*T:=by
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul parts
    exact (Nat.mul_le_mul ((Nat.succ_le_succ lanes).trans cube) (Nat.pow_le_pow_right (by decide) old)).trans shared
  have oldBand : N*H*chunks (G*X) a.oldBatch ≤ N*(a.shapes*T):=by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left N oldRows
  have newBand : N*H*chunks (G*X) (M*X) ≤ N*(a.shapes*T):=by
    rw [Nat.mul_assoc];exact Nat.mul_le_mul_left N ((Nat.mul_le_mul_left H crossed).trans groupCount)
  have projectTable : X*2^((a.metaBits*X)*M) ≤ X*T:=Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) project).trans page)
  have reshapeFields : N*DescentVectorBookReshape.rows H 1 G X M ≤ N*(X*(a.shapes*T)):=by
    simp only [DescentVectorBookReshape.rows,Nat.mul_one]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ groupCount)
  have data : N ≤ N*T:=Nat.le_mul_of_pos_right _ one
  have total : DescentResetStemProject.volume N H G X a.metaBits a.oldBatch M≤
      N*T+N*(a.shapes*T)+N*(a.shapes*T)+(X+2)*T+X*T+N*(X*(a.shapes*T))+a.shapes*T+T :=by
    dsimp only [DescentResetStemProject.volume,Overlap.rows,DescentVectorBookReshape.dictionaryWords]
    gcongr
  change 5000*(a.count+DescentResetStemProject.volume N H G X a.metaBits a.oldBatch M) ≤ a.volumeFactor*T
  apply (Nat.mul_le_mul_left 5000 (Nat.add_le_add stock total)).trans
  dsimp only [volumeFactor,N,X]
  ring_nf
  omega

end
end Hierarchy.DescentPrivateMaskDeck.Shape

end OAI
