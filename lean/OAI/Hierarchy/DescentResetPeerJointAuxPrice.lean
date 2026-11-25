import OAI.Hierarchy.DescentResetPeerJointAux
import OAI.Hierarchy.DescentResetPeerJointPackedPrice

namespace OAI
/-! # Native work for all four auxiliary coordinates of the packed peer table -/
namespace Hierarchy.DescentResetPeerJointPacked.Aux
open DescentResetPeerJointRAM DescentStaticWordColumn DescentSixParty.Chronology
open ProtocolRAM

open private DescentResetPeerJointRAM.bound from OAI.Hierarchy.DescentResetPeerJointPrice in
theorem scalar_work (A : Sources) (raw : Bank) (base P O D v col : ℕ) :
    (scalar A raw base P O D v col).work ≤ 300*(D+1) := by
  by_cases original : col=3
  · simpa only [scalar,ite_eq_left original] using DescentResetPeerOldCorrection.work A base P O D v
  let here := Expr.lookup A.inverse (.lit v)
  let root := Expr.lookup (table base P 0) here
  let first := Expr.lookup (table base P 2) here
  let ports := fun i : Fin D => Expr.lookup A.prior (.op .add first (.lit i.val))
  let shape := if col=0 then Expr.lit 0 else .lookup (table base P 1) here
  by_cases absent : col=2
  · simp only [scalar,ite_eq_right original,ite_eq_left absent]
    change 1+6+(DescentResetPeerMissingSelf.missing raw P here).work+1+1 ≤ _
    rw [DescentResetPeerMissingSelf.work]
    change 1+6+(6*6+28)+1+1 ≤ 300*(D+1)
    omega
  · have shapeWork : shape.work≤39 := by
      unfold shape
      split
      · exact (by decide : 1≤39)
      · exact (by decide : 11≤39)
    have chipCost := DescentResetPeerJointRAM.bound ports root root shape (fun _ => Nat.le_refl 18)
      (Nat.le_refl 11) (by decide : 11≤39) shapeWork
    simp only [scalar,ite_eq_right original,ite_eq_right absent]
    change 1+6+(11+1+(DescentClosedHaloChip.chip ports root root shape).work+1+1)+1+1 ≤ _
    omega

theorem priced (w base H P O width D G M b : ℕ) (A : Sources) (raw : Bank) :
    let phase := complete w base H P O width D G M b A raw
    phase.ticks+names phase.program ≤ 18000*(H+1)*(D+1)+150*(P+1)+
      25*DescentResetPeerJointBroadcast.count H G M b+38 := by
  intro phase
  let first := DescentResetPeerJointPacked.phase w base H P O width D G M b A
  let start := DescentResetPeerJointPacked.endAddress base H P G M b
  let last := writer w start base H P O D A raw
  have «prefix» := DescentResetPeerJointPacked.priced w base H P O width D G M b A
  change first.ticks+names first.program ≤ _ at «prefix»
  have extra : last.ticks+names last.program ≤ 19+4*H*(19+6*(300*(D+1))) :=
    DescentFixedRowProgram.bill w start (4*H) (row A raw base H P O D) (300*(D+1))
      (fun i _ => scalar_work A raw base P O D (i%H) (i/H))
  change first.ticks+last.ticks+names (first.program.seq last.program) ≤ _
  rw [names_seq]
  ring_nf at «prefix» extra ⊢
  omega

end Hierarchy.DescentResetPeerJointPacked.Aux

end OAI
