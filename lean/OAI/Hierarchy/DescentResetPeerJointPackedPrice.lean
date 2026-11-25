import OAI.Hierarchy.DescentResetPeerJointPacked
import OAI.Hierarchy.DescentResetPeerJointPrice

namespace OAI
/-! # Actual runtime and instruction names of the four packed joint peer ranks -/
namespace Hierarchy.DescentResetPeerJointPacked
open DescentStaticWordColumn DescentSixParty.Chronology

theorem priced (w base H P O width D G M b : ℕ) (A : DescentResetPeerJointRAM.Sources) :
    let pgm:=phase w base H P O width D G M b A
    pgm.ticks + names pgm.program ≤ 9000*(H+1)*(D+1)+150*(P+1)+
      25*DescentResetPeerJointBroadcast.count H G M b+19 := by
  let stop:=DescentResetPeerJointRAM.endAddress base H P
  let first:=DescentResetPeerJointRAM.phase w base H P O width D A
  let n:=DescentResetPeerJointBroadcast.count H G M b
  have head := DescentResetPeerJointRAM.price w base H P O width D A
  change first.ticks+names first.program≤_ at head
  change first.ticks+(4+10*n)+names (first.program.seq (DescentResetPeerJointBroadcast.program w stop H G M b)) ≤ _
  rw [names_seq,DescentResetPeerJointBroadcast.names]
  change first.ticks+(4+10*n)+(names first.program+15*(n+1))≤9000*(H+1)*(D+1)+150*(P+1)+25*n+19
  omega

end Hierarchy.DescentResetPeerJointPacked

end OAI
